import FVTest.Backend.StockCheckCallsWitness
import FV.E2E.MidValPass

/-! # Witness: the Stock path's theorem through the mid-end validator (#1119)

A real pair of the measured release crates (sha3 0.12.0's `cargo fv test --release --midval`,
dependency keccak 0.2.x, `_RNxC6keccak12HbPukoXULhhU`): the split CLIF `cargo fv` handed
`lean-backend` (`<stem>.unopt.clif`, cg_clif's source function `f`) and the optimised dump
(`<stem>.opt.clif`, Cranelift's function `g`). Cranelift forwarded the value stored to `ss0` in
`block0` to the load of `ss0` in `block1` (the call's third argument becomes `v1`) and removed the
`nop`s and the second `stack_addr`. `lean-backend --midval-opt` decided `Opt.MidVal.checkCert` on
the pair and compiled `g` on the Stock path, naming
`E2E.backend_correct_midval_semantic_return_pins`.

`midval_applies` instantiates that theorem with **no assumed checkable premise**: the re-check of
the certificate `Opt.MidVal.emit` gives (`midOk`), the Stock artifact of the compiled `g`
(`StockCheckCallsWitness.witness`, its `SemanticABI.checkCalls` from the driver's route), `InSubset`
(`InSubset.of_verifiable`, a function-free program) and `FormsCovered` (`formsCoveredB_iff`); the
program of validated functions is the empty one (`Opt.MidVal.Validated.nil`). Left open, as in every
per-function theorem: the run and environment hypotheses. The facts are decided by `native_decide`
(a witness, not a compiler theorem); they include that the compiled function is `g` itself (no
legalisation or constant-phi change) and that `g` is not `f` after constant-phi removal. -/

namespace FVTest.Backend.MidValPassWitness
open _root_.Backend _root_.Backend.Proof _root_.Backend.Proof.Driver E2E
open FVTest.Backend.StockCheckCallsWitness (first f vcp rf af fa fb facts witness)
set_option autoImplicit false

/-- `_RNxC6keccak12HbPukoXULhhU` (keccak, sha3 0.12.0's release build): `<stem>.unopt.clif`. -/
def srcF : String := "set regalloc_algorithm=backtracking\nset opt_level=speed_and_size\nset tls_model=elf_gd\nset stack_switch_model=none\nset libcall_call_conv=isa_default\nset probestack_size_log2=12\nset probestack_strategy=inline\nset bb_padding_log2_minus_one=0\nset log2_min_function_alignment=0\nset regalloc_checker=0\nset regalloc_verbose_logs=0\nset enable_alias_analysis=1\nset enable_verifier=0\nset is_pic=1\nset use_colocated_libcalls=0\nset enable_nan_canonicalization=0\nset enable_pinned_reg=0\nset enable_llvm_abi_extensions=1\nset enable_multi_ret_implicit_sret=0\nset unwind_info=1\nset preserve_frame_pointers=1\nset machine_code_cfg_info=0\nset enable_probestack=1\nset enable_heap_access_spectre_mitigation=1\nset enable_table_access_spectre_mitigation=1\nset enable_incremental_compilation_cache_checks=0\nset enable_compact_unwind_abi=0\ntarget aarch64 has_lse=0 has_pauth=0 has_fp16=0 has_dotprod=0 has_i8mm=0 sign_return_address_all=0 sign_return_address=0 sign_return_address_with_bkey=0 use_bti=0 use_csdb=0\n\nfunction %_RNxC6keccak12HbPukoXULhhU(i64, i64, i64) -> i64, i64 system_v {\n    ss0 = explicit_slot 8, align = 8\n    sig0 = (i64, i64, i64, i64) -> i64, i64 system_v\n    fn0 = colocated %_RNxC6keccak12H2JZHOfvwFOl(i64, i64, i64, i64) -> i64, i64 system_v\n\nblock0(v0: i64, v1: i64, v2: i64):\n    nop\n    v3 = stack_addr.i64 ss0\n    store.i64 notrap v1, v3\n    jump block1\n\nblock1:\n    nop\n    v5 = iconst.i64 24\n    v6 = stack_addr.i64 ss0\n    v7 = load.i64 notrap v6\n    nop\n    v8, v9 = call fn0(v0, v5, v7, v2)\n    jump block2\n\nblock2:\n    nop\n    return v8, v9\n}\n"

/-- The same function's `<stem>.opt.clif` (Cranelift's optimised function). -/
def srcG : String := "set regalloc_algorithm=backtracking\nset opt_level=speed_and_size\nset tls_model=elf_gd\nset stack_switch_model=none\nset libcall_call_conv=isa_default\nset probestack_size_log2=12\nset probestack_strategy=inline\nset bb_padding_log2_minus_one=0\nset log2_min_function_alignment=0\nset regalloc_checker=0\nset regalloc_verbose_logs=0\nset enable_alias_analysis=1\nset enable_verifier=0\nset is_pic=1\nset use_colocated_libcalls=0\nset enable_nan_canonicalization=0\nset enable_pinned_reg=0\nset enable_llvm_abi_extensions=1\nset enable_multi_ret_implicit_sret=0\nset unwind_info=1\nset preserve_frame_pointers=1\nset machine_code_cfg_info=0\nset enable_probestack=1\nset enable_heap_access_spectre_mitigation=1\nset enable_table_access_spectre_mitigation=1\nset enable_incremental_compilation_cache_checks=0\nset enable_compact_unwind_abi=0\ntarget aarch64 has_lse=0 has_pauth=0 has_fp16=0 has_dotprod=0 has_i8mm=0 sign_return_address_all=0 sign_return_address=0 sign_return_address_with_bkey=0 use_bti=0 use_csdb=0\n\nfunction %_RNxC6keccak12HbPukoXULhhU(i64, i64, i64) -> i64, i64 system_v {\n    ss0 = explicit_slot 8, align = 8\n    sig0 = (i64, i64, i64, i64) -> i64, i64 system_v\n    fn0 = colocated %_RNxC6keccak12H2JZHOfvwFOl(i64, i64, i64, i64) -> i64, i64 system_v\n\nblock0(v0: i64, v1: i64, v2: i64):\n    nop\n    v3 = stack_addr.i64 ss0\n    store.i64 notrap v1, v3\n    jump block1\n\nblock1:\n    v5 = iconst.i64 24\n    v8, v9 = call fn0(v0, v5, v1, v2)\n    jump block2\n\nblock2:\n    return v8, v9\n}\n"

/-- The source function, as `lean-backend` parses its input. -/
def fSrc : Clif.Function := ((first (Clif.parseFile srcF).funcs).func.toOption).getD default

/-- Cranelift's optimised function, as `lean-backend --midval-opt` parses it. -/
def gOpt : Clif.Function := ((first (Clif.parseFile srcG).funcs).func.toOption).getD default

/-- What `lean-backend --midval-opt` decides (`midvalDecide`): the re-check of the certificate
`Opt.MidVal.emit` gives. -/
def midOk (f g : Clif.Function) : Bool :=
  match Opt.MidVal.emit (Opt.ConstPhi.run f) g with
  | .ok cert => Opt.MidVal.checkCert (Opt.ConstPhi.run f) g cert
  | .error _ => false

/-- What `native_decide` evaluates: the driver's run on the optimised file compiled it on the
Stock path with the objects of `StockCheckCallsWitness` (`facts`), the compiled function is `g`
itself, `Backend.verifiable`, `formsCoveredB`, the re-check, and `g` differs from `f` after
constant-phi removal. -/
def factsMid : Bool :=
  facts srcG && decide (f srcG = gOpt) && Backend.verifiable (f srcG) &&
  formsCoveredB ⟨(fa srcG).k, (af srcG).slotBase⟩ (vcp srcG) && midOk fSrc (f srcG) &&
  !decide (Opt.ConstPhi.run fSrc = gOpt)

theorem factsMid0 : factsMid = true := by native_decide

/-- The checkable premises of `backend_correct_midval_semantic_return_pins` hold for the pair. -/
theorem premises (h : factsMid = true) :
    (∃ cert, Opt.MidVal.checkCert (Opt.ConstPhi.run fSrc) (f srcG) cert = true) ∧
    ∃ vc, CompiledSemanticReturnPins (f srcG) 0 vc (vcp srcG) (rf srcG) (af srcG) (fa srcG)
        (fb srcG) (ReturnPinMode.checked (f srcG) vc) ∧
      InSubset { funcs := [] } (f srcG) ∧
      FormsCovered ⟨(fa srcG).k, (af srcG).slotBase⟩ (vcp srcG) := by
  simp only [factsMid, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hfacts, -⟩, hv⟩, hcov⟩, hmid⟩, -⟩ := h
  obtain ⟨-, -, vc, -, -, hc⟩ := witness srcG hfacts
  refine ⟨?_, vc, hc, InSubset.of_verifiable hv (fun _ => rfl), (formsCoveredB_iff _ _).mp hcov⟩
  unfold midOk at hmid
  split at hmid
  · exact ⟨_, hmid⟩
  · cases hmid

/-- **`backend_correct_midval_semantic_return_pins` applies to the compiled pair**: every return of
the run of cg_clif's source function `fSrc` is matched by the Arm run of the code `lean-backend`
emitted for Cranelift's optimised function, under the run and environment hypotheses only. -/
theorem midval_applies {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat} {F : BitVec 64 → Prop} {c : BitVec 64}
    (hX : XCallsOk env (fSrc.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute (vcp srcG) (rf srcG)).intBase⟩ fSrc c) X)
    (hXI : XCallsIndOk env (indSigs (f srcG))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute (vcp srcG) (rf srcG)).intBase⟩ fSrc c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : (af srcG).slotBase = slotOff)
    (hE : Opt.EnvKeepsSymbols env)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry fSrc args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute (vcp srcG) (rf srcG)).intBase⟩ fSrc c
      cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F fSrc.sig args w₀)
    (htr : TrapsExplicit env { funcs := [] } (midEntry (f srcG) cs)) (fuel : Nat) :
    ∃ (vc : VCode) (mode : ReturnPinMode),
    ∀ vals cm, Clif.runLoop env { funcs := [] } fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        ReturnPinMode.Valid mode fSrc vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry (vcp srcG) (rf srcG) (af srcG) (fa srcG) (fb srcG) K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H (fa srcG)) n s) ∧
            PostTrace (fa srcG) (af srcG) base (ArmStepX X H (fa srcG)) s n ∧
            ∀ i < n, actGoodX (vcp srcG) (rf srcG) (af srcG) (fa srcG) (fb srcG) base s X H K G
              (GotV (vcp srcG)) (runX (ArmStepX X H (fa srcG)) i s)) ∧
        (XNI F syms (fSrc.externs.map (·.2)) (indSigs (f srcG)) c
          (CallLg env (fSrc.externs.map (·.2)) (indSigs (f srcG))) X → XTls F X →
        ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute (vcp srcG) (rf srcG)).intBase⟩ fSrc c
            cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf fSrc.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf fSrc.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
            ActEntry (vcp srcG) (rf srcG) (af srcG) (fa srcG) (fb srcG) K F G X H base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (ArmStepX X H (fa srcG)) n s) ∧
              PostTrace (fa srcG) (af srcG) base (ArmStepX X H (fa srcG)) s n ∧
              ∀ i < n, actGoodX (vcp srcG) (rf srcG) (af srcG) (fa srcG) (fb srcG) base s X H K G
                (GotV (vcp srcG)) (runX (ArmStepX X H (fa srcG)) i s)) := by
  obtain ⟨⟨cert, hchk⟩, vc, hc, hsub, hcov⟩ := premises factsMid0
  exact ⟨vc, _, backend_correct_midval_semantic_return_pins (K := K) hchk
    (p := { funcs := [] }) (q := { funcs := [] }) Opt.MidVal.Validated.nil hsub hc hcov hX hXI hsym
    hslot hE hcs hrel hargs htr fuel⟩

end FVTest.Backend.MidValPassWitness
