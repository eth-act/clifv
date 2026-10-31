import FV.E2E.CompiledAnyT
import FV.E2E.SemanticNIBoundary
import FV.E2E.SretReturn

/-!
# Either typed artifact, or the Stock artifact of an integer function (#722)

`CompiledAnyTS p f …` is `CompiledAnyT p f …` (the typed artifacts of `lowerFunction`'s output)
or `CompiledStockT p f …`: an integer function (`InSubset`) without `sret` parameter whose
artifact is the Stock route's (`CompiledSemanticNI`, from `SemanticNI.check`: Cranelift's code
where the Stock lowerings are proven). It is the artifact contract of `LinkSys.OkT` (widened in
place, as S11e6/S11f widened it), so the typed link layer describes an executable whose integer
functions are compiled by the Stock lowerings and whose other functions by `lowerFunction`.

The projections and the four dispatch theorems `backend_correct_world{,_ni,X,_niX}_pipelineAnyTS`
have the conclusions of the `…_pipelineAnyTF` ones. The Stock case is the integer world theorem
(`backend_correct_world…_semantic`) with its returns pinned by `RetPins` read by class (`retRegsOk_of_retPins`):
a run of an integer function returns integers of its return types
(`returned_tys_stock`, `returned_int_stock`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

theorem classes_int {rvals : List Clif.Val} (hint : ∀ v ∈ rvals, v.ty.isInt = true) :
    rvals.map (fun v => tyClass v.ty) = List.replicate rvals.length .int := by
  rw [List.eq_replicate_iff]
  simp only [List.length_map, List.mem_map, true_and]
  rintro _ ⟨v, hv, rfl⟩
  simp only [tyClass, hint v hv, ite_true]

/-- Integer returns in x0.. are in their classes' return registers. With exactly as many
returned registers as values (`hle`; #587: `RetRegsOk` puts any extra ABI return, an `sret`
function's struct pointer, in x8, so the pre-#587 statement with `≤` became false). -/
theorem retRegsOk_of_x {rvals : List Clif.Val} {us : List (Reg × Reg)}
    (hus : us.map (·.2) = (List.range us.length).map Reg.x)
    (hint : ∀ v ∈ rvals, v.ty.isInt = true) (hle : rvals.length = us.length) :
    RetRegsOk rvals us := by
  refine ⟨[], ?_⟩
  rw [List.append_nil, List.take_of_length_le (by simp), classes_int hint, retRegsT_int,
    List.length_replicate, Nat.sub_self, List.replicate_zero, List.append_nil, hus, hle,
    List.range_eq_range']

/-- Integer returns pinned by `RetPins` (x0.., then x8) are in their classes' return registers. -/
theorem retRegsOk_of_retPins {rvals : List Clif.Val} {us : List (Reg × Reg)}
    (hus : RetPins rvals us)
    (hint : ∀ v ∈ rvals, v.ty.isInt = true) (hle : rvals.length ≤ us.length) :
    RetRegsOk rvals us := by
  refine ⟨List.replicate (us.length - rvals.length) .int, ?_⟩
  unfold RetPins at hus
  rw [classes_int hint, List.replicate_append_replicate, Nat.add_sub_cancel' hle,
    List.take_replicate, Nat.min_eq_left hle, retRegsT_int, List.length_replicate, hus,
    map_retX_ge hle, List.range_eq_range']

/-- **Every return of `vc` is in its `retX` register** (#722): the condition under which the typed
link layer (`LinkSys.OkT.sretE`) admits an `sret` function outside subset E, for a function of
`k` declared returns: the first `k` in x0.., the rest (the struct pointer that `lowerFunction`
appends to an `sret` function's returns) in x8. Before #587 this said x0, x1, … throughout; the
compiler now returns the struct pointer in x8, as Cranelift does, so that form no longer held
of any `sret` function's code. -/
def RetsX (k : Nat) (vc : VCode) : Prop :=
  ∀ us, vc.RetsSite us → us.map (·.2) = (List.range us.length).map (retX k)

/-- **The Stock artifact of an integer function** (#722): an integer function (`InSubset`)
without `sret` parameter, with the Stock route's artifact contract (`CompiledSemanticNI`). -/
def CompiledStockT (p : Clif.Program) (f : Clif.Function) (k : Nat) (vc vcp : VCode) (rf : RFunc)
    (af : AFunc) (fa : FnAsm) (fb : FnBin) : Prop :=
  InSubset p f ∧ f.sig.params.any (·.purpose == .sret) = false ∧
    CompiledSemanticNI f k vc vcp rf af fa fb

/-- **The artifact contract of the typed link layer** (#722): either typed artifact
(`CompiledAnyT`) or the Stock artifact of an integer function (`CompiledStockT`). -/
def CompiledAnyTS (p : Clif.Program) (f : Clif.Function) (k : Nat) (vc vcp : VCode) (rf : RFunc)
    (af : AFunc) (fa : FnAsm) (fb : FnBin) : Prop :=
  CompiledAnyT p f k vc vcp rf af fa fb ∨ CompiledStockT p f k vc vcp rf af fa fb

namespace CompiledAnyTS
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

theorem check (h : CompiledAnyTS p f k vc vcp rf af fa fb) : checkAlloc vcp rf = .ok () := by
  rcases h with h | ⟨-, -, h⟩
  · exact h.check
  · exact h.check

theorem alloc (h : CompiledAnyTS p f k vc vcp rf af fa fb) : lowerRFunc vcp rf = .ok af := by
  rcases h with h | ⟨-, -, h⟩
  · exact h.alloc
  · exact h.alloc

theorem emit (h : CompiledAnyTS p f k vc vcp rf af fa fb) : emitFunc k af = .ok fa := by
  rcases h with h | ⟨-, -, h⟩
  · exact h.emit
  · exact h.emit

theorem layout (h : CompiledAnyTS p f k vc vcp rf af fa fb) : fa.layout = .ok fb := by
  rcases h with h | ⟨-, -, h⟩
  · exact h.layout
  · exact h.layout

/-- The entry registers of the artifact's signature (`CompiledAnyT.entryRegs`; x0..x8 for the
Stock artifact, `CompiledSemanticNI.entryRegs`). -/
theorem entryRegs (h : CompiledAnyTS p f k vc vcp rf af fa fb) :
    ∀ l ∈ locsOf f.sig, ∀ r, l = .reg r → (∃ n, r = .x n ∧ n ≤ 8) ∨ (∃ n, r = .v n ∧ n ≤ 7) := by
  rcases h with h | ⟨-, -, h⟩
  · exact h.entryRegs
  · exact fun l hl r hr => .inl (h.entryRegs l hl r hr)

end CompiledAnyTS

/-- `hasTls_of_vcode_pipelineAnyT` for `CompiledAnyTS`. -/
theorem hasTls_of_vcode_pipelineAnyTS {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hc : CompiledAnyTS p f k vc vcp rf af fa fb) (ht : vcp.hasTls = true) :
    hasTls f = true := by
  rcases hc with hc | ⟨-, -, hc⟩
  · exact hasTls_of_vcode_pipelineAnyT hc ht
  · exact hasTls_of_vcode_semantic hc ht

/-- A function without `sret` parameter appends no value to its returns (`sretRet`), so its
`sret` value is trivially stable. -/
theorem sretStable_of_noSret {f : Clif.Function} (h : f.sig.params.any (·.purpose == .sret) = false) :
    SretStable f := by
  have hnil : sretRet f = [] := by
    unfold sretRet
    rw [sigRets_of_noSret h]
    simp
  exact ⟨fun x hx => by simp [hnil] at hx, fun x hx => by simp [hnil] at hx,
    fun x hx => by simp [hnil] at hx, fun x hx => by simp [hnil] at hx⟩

/-- **A run of an integer function without `sret` parameter from its entry returns values of its
return types.** -/
theorem returned_tys_stock {p : Clif.Program} {f : Clif.Function} {env : Clif.Env}
    {args : List Clif.Val} {cs : Clif.State} (hsub : InSubset p f)
    (hns : f.sig.params.any (·.purpose == .sret) = false) (hcs : ClifEntry f args cs)
    (htr : TrapsExplicit env p cs) {fuel : Nat} {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop env p fuel cs = .returned vals cm) :
    vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns := by
  obtain ⟨B0, hentB, hbody, hterm, -, -⟩ := hcs.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hentB
  exact runLoop_returned_tys_entry hsub.externCalls hsub.tryExterns (noTail_of_subset hsub)
    (runPrem_of_entry hcs htr) (sretStable_of_noSret hns) hB0 hcs.callers hcs.func hbody hterm hrun

/-- **A run of an integer function without `sret` parameter from its entry returns integers.** -/
theorem returned_int_stock {p : Clif.Program} {f : Clif.Function} {env : Clif.Env}
    {args : List Clif.Val} {cs : Clif.State} (hsub : InSubset p f)
    (hns : f.sig.params.any (·.purpose == .sret) = false) (hcs : ClifEntry f args cs)
    (htr : TrapsExplicit env p cs) {fuel : Nat} {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop env p fuel cs = .returned vals cm) :
    ∀ v ∈ vals, v.ty.isInt = true := by
  intro v hv
  have hm : v.ty ∈ Clif.AbiParam.tys f.sig.returns :=
    returned_tys_stock hsub hns hcs htr hrun ▸ List.mem_map_of_mem hv
  obtain ⟨q, hq, hqt⟩ := List.mem_map.mp hm
  have hE := hsub.subsetE
  simp only [Compile.functionE, Compile.sigE, Bool.and_eq_true, List.all_eq_true] at hE
  have := hE.1.1.1.2 q hq
  simp only [Compile.tyE, Bool.and_eq_true] at this
  rw [← hqt]; exact this.1

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin} {X : ExtSem} {syms : String → Option Nat}
  {slotOff : Nat} {env : Clif.Env} {F : BitVec 64 → Prop} {c : BitVec 64}

/-- **The typed world theorem for either typed artifact or the Stock artifact of an integer
function** (`backend_correct_world_pipelineAnyTF`'s conclusion, literally). -/
theorem backend_correct_world_pipelineAnyTS (hsub : InSubsetTCF p f)
    (hc : CompiledAnyTS p f k vc vcp rf af fa fb)
    (hT : TypedRules) {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetRegsOk vals us ∧ vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns ∧
        us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s)) := by
  rcases hc with hc | ⟨hsubS, hns, hc⟩
  · exact backend_correct_world_pipelineAnyTF hsub hc hT hcov hX hXI hsym hslot hcs hrel hargs
      htr fuel
  · obtain ⟨hret, htrap⟩ := backend_correct_world_semantic (K := K) hsubS hc hcov hX hXI hsym
      hslot hcs hrel hargs htr fuel
    refine ⟨fun vals cm hrun => ?_, htrap⟩
    obtain ⟨us, outs, w, hus, hlen, hhold, hmem, hrs, hall⟩ := hret vals cm hrun
    exact ⟨us, outs, w,
      retRegsOk_of_retPins hus (returned_int_stock hsubS hns hcs htr hrun) (by have := hhold.1; omega),
      returned_tys_stock hsubS hns hcs htr hrun, hlen, hhold, hmem, hrs, hall⟩

/-- **The typed world theorem with non-interference for either typed artifact or the Stock
artifact of an integer function** (`backend_correct_world_ni_pipelineAnyTF`'s conclusion,
literally). -/
theorem backend_correct_world_ni_pipelineAnyTS (hsub : InSubsetTCF p f)
    (hc : CompiledAnyTS p f k vc vcp rf af fa fb)
    (hT : TypedRules) {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetRegsOk vals us ∧ vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns ∧
        us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n) ∧
        (XNI F syms (f.externs.map (·.2)) (indSigs f) c
          (CallLg env (f.externs.map (·.2)) (indSigs f)) X → XTls F X →
        ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
            ActEntry vcp rf af fa fb K F G X H base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (ArmStepX X H fa) n s) ∧
              PostTrace fa af base (ArmStepX X H fa) s n) := by
  rcases hc with hc | ⟨hsubS, hns, hc⟩
  · exact backend_correct_world_ni_pipelineAnyTF hsub hc hT hcov hX hXI hsym hslot hcs hrel hargs
      htr fuel
  · intro vals cm hrun
    obtain ⟨us, outs, w, hus, hlen, hhold, hmem, hrs, hall, hni⟩ :=
      backend_correct_world_ni_semantic (K := K) hsubS hc hcov hX hXI hsym hslot hcs hrel hargs
        htr fuel vals cm hrun
    exact ⟨us, outs, w,
      retRegsOk_of_retPins hus (returned_int_stock hsubS hns hcs htr hrun) (by have := hhold.1; omega),
      returned_tys_stock hsubS hns hcs htr hrun, hlen, hhold, hmem, hrs, hall, hni⟩

/-- **The typed per-state world theorem for either typed artifact or the Stock artifact of an
integer function** (`backend_correct_worldX_pipelineAnyTF`'s conclusion, literally). -/
theorem backend_correct_worldX_pipelineAnyTS (hsub : InSubsetTCF p f)
    (hc : CompiledAnyTS p f k vc vcp rf af fa fb)
    (hT : TypedRules) {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetRegsOk vals us ∧ vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns ∧
        us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s)) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s) ∧
          (∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
            (runX (ArmStepX X H fa) i s)) ∧
          ∀ m, Arm.r .ERR (runX (ArmStepX X H fa) (n + m + 1) s) ≠ .None) := by
  rcases hc with hc | ⟨hsubS, hns, hc⟩
  · exact backend_correct_worldX_pipelineAnyTF hsub hc hT hcov hX hXI hsym hslot hcs hrel hargs
      htr fuel
  · obtain ⟨hret, htrap⟩ := backend_correct_worldX_semantic (K := K) hsubS hc.toSemantic hcov hX
      hXI hsym hslot hcs hrel hargs htr fuel
    refine ⟨fun vals cm hrun => ?_, htrap⟩
    obtain ⟨us, outs, w, hus, hlen, hhold, hmem, hrs, hall⟩ := hret vals cm hrun
    exact ⟨us, outs, w,
      retRegsOk_of_retPins hus (returned_int_stock hsubS hns hcs htr hrun) (by have := hhold.1; omega),
      returned_tys_stock hsubS hns hcs htr hrun, hlen, hhold, hmem, hrs, hall⟩

/-- **The typed per-state world theorem with non-interference for either typed artifact or the
Stock artifact of an integer function** (`backend_correct_world_niX_pipelineAnyTF`'s conclusion,
literally). -/
theorem backend_correct_world_niX_pipelineAnyTS (hsub : InSubsetTCF p f)
    (hc : CompiledAnyTS p f k vc vcp rf af fa fb)
    (hT : TypedRules) {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetRegsOk vals us ∧ vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns ∧
        us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s)) ∧
        (XNI F syms (f.externs.map (·.2)) (indSigs f) c
          (CallLg env (f.externs.map (·.2)) (indSigs f)) X → XTls F X →
        ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
            ActEntry vcp rf af fa fb K F G X H base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (ArmStepX X H fa) n s) ∧
              PostTrace fa af base (ArmStepX X H fa) s n ∧
              ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
                (runX (ArmStepX X H fa) i s)) := by
  rcases hc with hc | ⟨hsubS, hns, hc⟩
  · exact backend_correct_world_niX_pipelineAnyTF hsub hc hT hcov hX hXI hsym hslot hcs hrel
      hargs htr fuel
  · intro vals cm hrun
    obtain ⟨us, outs, w, hus, hlen, hhold, hmem, hrs, hall, hni⟩ :=
      backend_correct_world_niX_semantic (K := K) hsubS hc hcov hX hXI hsym hslot hcs hrel hargs
        htr fuel vals cm hrun
    exact ⟨us, outs, w,
      retRegsOk_of_retPins hus (returned_int_stock hsubS hns hcs htr hrun) (by have := hhold.1; omega),
      returned_tys_stock hsubS hns hcs htr hrun, hlen, hhold, hmem, hrs, hall, hni⟩

end

end E2E
