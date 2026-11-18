import FVTest.Backend.StockCheckCallsWitness
import FV.E2E.SemanticReturnPinsPass
import FV.E2E.ConstPhiE2E

/-! # Witness: the Stock path's theorem composed with constant-phi removal (#1100)

A real function `lean-backend` compiles for `examples/fv-demo` (`_RNxC7fv_demo12H62jtQXrlYqO`, the
split CLIF `cargo fv` handed `lean-backend`, one function per file). Constant-phi removal changes
it (`Opt.ConstPhi.keeps`: it removes the unreachable blocks `block2`, `block4`), and the driver
compiles `Opt.ConstPhi.run g` of its source `g` on the Stock path (`compileFileReturnPinWhen true`,
`FVTest.Backend.StockCheckCallsWitness.run`).

`pass_applies` instantiates `E2E.backend_correct_pass_semantic_return_pins (T := Opt.ConstPhi.run)`
on it with **no assumed checkable premise**: the pass's facts (`Opt.ConstPhi.run_simX`,
`Opt.ConstPhi.run_shape`), `InSubset` of the source (`InSubset.of_verifiable`, a function-free
program), the Stock artifact of the compiled function (`StockCheckCallsWitness.witness`, its
`SemanticABI.checkCalls` from the driver's route, #1101) and `FormsCovered` (`formsCoveredB_iff`).
Left open, as in every per-function theorem: the run and environment hypotheses. The facts about
the run and the compiled objects (`factsCp`) are decided by `native_decide` (a witness, not a
compiler theorem). -/

namespace FVTest.Backend.SemanticReturnPinsPassWitness
open _root_.Backend _root_.Backend.Proof _root_.Backend.Proof.Driver E2E
open FVTest.Backend.StockCheckCallsWitness (legal first p f vcp rf af fa fb facts witness)
set_option autoImplicit false

/-- `_RNxC7fv_demo12H62jtQXrlYqO` (examples/fv-demo) -/
def srcCp : String := "set regalloc_algorithm=backtracking\nset opt_level=none\nset tls_model=elf_gd\nset stack_switch_model=none\nset libcall_call_conv=isa_default\nset probestack_size_log2=12\nset probestack_strategy=inline\nset bb_padding_log2_minus_one=0\nset log2_min_function_alignment=0\nset regalloc_checker=0\nset regalloc_verbose_logs=0\nset enable_alias_analysis=1\nset enable_verifier=0\nset is_pic=1\nset use_colocated_libcalls=0\nset enable_nan_canonicalization=0\nset enable_pinned_reg=0\nset enable_llvm_abi_extensions=1\nset enable_multi_ret_implicit_sret=0\nset unwind_info=1\nset preserve_frame_pointers=1\nset machine_code_cfg_info=0\nset enable_probestack=1\nset enable_heap_access_spectre_mitigation=1\nset enable_table_access_spectre_mitigation=1\nset enable_incremental_compilation_cache_checks=0\nset enable_compact_unwind_abi=0\ntarget aarch64 has_lse=0 has_pauth=0 has_fp16=0 has_dotprod=0 has_i8mm=0 sign_return_address_all=0 sign_return_address=0 sign_return_address_with_bkey=0 use_bti=0 use_csdb=0\n\nfunction %_RNxC7fv_demo12H62jtQXrlYqO(i64) system_v {\n    ss0 = explicit_slot 8, align = 8\n\nblock0(v0: i64):\n    nop\n    v1 = stack_addr.i64 ss0\n    store.i64 notrap v0, v1\n    jump block1\n\nblock1:\n    nop\n    v2 = iconst.i8 0\n    jump block3\n\nblock2:\n    trap user1\n\nblock3:\n    nop\n    return\n\nblock4:\n    trap user1\n}\n"

/-- The source function before constant-phi removal (after the `i128` legalisation). -/
def g (src : String) : Clif.Function := ((first (legal src).file.funcs).func.toOption).getD default

/-- What `native_decide` evaluates: `StockCheckCallsWitness.facts` (the driver's run compiled the
function on the Stock path, with the objects below), constant-phi removal changed it and the driver
compiled `Opt.ConstPhi.run` of the source, the source is `Backend.verifiable`, `formsCoveredB`. -/
def factsCp (src : String) : Bool :=
  facts src && Opt.ConstPhi.keeps (Link.clifHeader src) (g src) &&
  decide (f src = Opt.ConstPhi.run (g src)) && Backend.verifiable (g src) &&
  formsCoveredB ⟨(fa src).k, (af src).slotBase⟩ (vcp src)

theorem factsCp0 : factsCp srcCp = true := by native_decide

/-- The checkable premises of `backend_correct_pass_semantic_return_pins` hold for the run. -/
theorem premises (src : String) (h : factsCp src = true) :
    ∃ vc, CompiledSemanticReturnPins (Opt.ConstPhi.run (g src)) 0 vc (vcp src) (rf src) (af src)
        (fa src) (fb src) (ReturnPinMode.checked (f src) vc) ∧
      InSubset { funcs := [] } (g src) ∧ FormsCovered ⟨(fa src).k, (af src).slotBase⟩ (vcp src) := by
  simp only [factsCp, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hfacts, -⟩, hrun⟩, hv⟩, hcov⟩ := h
  obtain ⟨-, -, vc, -, -, hc⟩ := witness src hfacts
  exact ⟨vc, hrun ▸ hc, InSubset.of_verifiable hv (fun _ => rfl), (formsCoveredB_iff _ _).mp hcov⟩

/-- **`backend_correct_pass_semantic_return_pins` applies to the compiled function**: every return
of the run of the source function (before constant-phi removal) is matched by the Arm run of the
code `lean-backend` emitted, under the run and environment hypotheses only. -/
theorem pass_applies {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat} {F : BitVec 64 → Prop} {c : BitVec 64}
    (hX : XCallsOk env ((g srcCp).externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute (vcp srcCp) (rf srcCp)).intBase⟩ (g srcCp) c) X)
    (hXI : XCallsIndOk env (indSigs (Opt.ConstPhi.run (g srcCp)))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute (vcp srcCp) (rf srcCp)).intBase⟩ (g srcCp) c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : (af srcCp).slotBase = slotOff)
    (hE : Opt.EnvKeepsSymbols env)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry (g srcCp) args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute (vcp srcCp) (rf srcCp)).intBase⟩ (g srcCp) c
      cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F (g srcCp).sig args w₀)
    (htr : TrapsExplicit env (passProg Opt.ConstPhi.run { funcs := [] })
      (passEntry Opt.ConstPhi.run (g srcCp) cs)) (fuel : Nat) :
    ∃ (vc : VCode) (mode : ReturnPinMode),
    ∀ vals cm, Clif.runLoop env { funcs := [] } fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        ReturnPinMode.Valid mode (g srcCp) vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry (vcp srcCp) (rf srcCp) (af srcCp) (fa srcCp) (fb srcCp) K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H (fa srcCp)) n s) ∧
            PostTrace (fa srcCp) (af srcCp) base (ArmStepX X H (fa srcCp)) s n ∧
            ∀ i < n, actGoodX (vcp srcCp) (rf srcCp) (af srcCp) (fa srcCp) (fb srcCp) base s X H K G
              (GotV (vcp srcCp)) (runX (ArmStepX X H (fa srcCp)) i s)) ∧
        (XNI F syms ((g srcCp).externs.map (·.2)) (indSigs (Opt.ConstPhi.run (g srcCp))) c
          (CallLg env ((g srcCp).externs.map (·.2)) (indSigs (Opt.ConstPhi.run (g srcCp)))) X →
          XTls F X →
        ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute (vcp srcCp) (rf srcCp)).intBase⟩ (g srcCp) c
            cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf (g srcCp).sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf (g srcCp).sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
            ActEntry (vcp srcCp) (rf srcCp) (af srcCp) (fa srcCp) (fb srcCp) K F G X H base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (ArmStepX X H (fa srcCp)) n s) ∧
              PostTrace (fa srcCp) (af srcCp) base (ArmStepX X H (fa srcCp)) s n ∧
              ∀ i < n, actGoodX (vcp srcCp) (rf srcCp) (af srcCp) (fa srcCp) (fb srcCp) base s X H K G
                (GotV (vcp srcCp)) (runX (ArmStepX X H (fa srcCp)) i s)) := by
  obtain ⟨vc, hc, hsub, hcov⟩ := premises srcCp factsCp0
  exact ⟨vc, _, backend_correct_pass_semantic_return_pins (T := Opt.ConstPhi.run)
    Opt.ConstPhi.run_simX Opt.ConstPhi.run_shape hsub hc hcov hX hXI hsym hslot hE hcs hrel hargs
    htr fuel⟩

end FVTest.Backend.SemanticReturnPinsPassWitness
