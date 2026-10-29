module

public import FVTest.E2E.FloatLinkT
public import FV.E2E.LinkScopeInputT

@[expose] public section

/-!
Non-vacuity of the typed input scope and the compiler's per-function totality on it (S11e5
Stage C, slice 8), on `FloatFinalT`'s `fW` (float `load`, `f64const`, `select`, `store`,
`bitcast` between integer parameters and return; outside subset E):

* `fW` is in `fnScopeInTB` (decided) and its typed lowering's `prepare` succeeds by the theorem
  (`Prep.prepare_okT`, `prepare_ok_cfgT`; integer: `prepare_ok_viaT` on `FloatLinkT.fInt`);
* the emission/allocation lemmas on `fW`'s prepared code (`ctlInsts_of_ctlInstsB`,
  `lowerRFunc_spillAllocT`, `backend_total_emitT`, `emitReady_spill_of`, `lowerAlloc_of_spill`,
  `lowerAllocReady_emit_of`);
* `fnScopeTB_of_inT`, `pipeT_okT` (any allocator answer), and on a one-function crate
  `resultsT_ok_inT`; integer inclusion `fnScopeInTB_of_fnScopeInB`/`fnScopeInB_of_fnScopeInTB`
  and `resultsT_ok_input` on `fInt`;
* `fBadStore` (a float store of an integer value) fails `fnScopeInTB`; `fnScopeInFailsT` names
  the failing conjuncts.
Checks by `native_decide` (witness only). `lake build FVTest.E2E.FloatTotalT`.
-/

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill E2E E2E.LinkCheck

namespace FloatTotalT

open FloatDriverT FloatFinalT FloatLinkT

#guard !Compile.functionE fW && fnScopeInTB fW && fnScopeInFailsT fW == []
#guard !fnScopeInTB fBadStore && (fnScopeInFailsT fBadStore).contains "storeTypedB"
#guard fnScopeInB fInt && fnScopeInTB fInt && !fnScopeInB fW

theorem fnScopeInTB_w : fnScopeInTB fW = true := by native_decide
theorem functionE_w : Compile.functionE fW = false := by native_decide
theorem dominated_w : Dominated fW := dominated_of (by native_decide)

/-- **Witness**: `fnScopeInT_parts` on `fW`. -/
theorem parts_w : Compile.functionET fW = true ∧ lowerScopeTB fW = true :=
  let h := fnScopeInT_parts fnScopeInTB_w
  ⟨h.1, h.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- **Witness**: `prepare` succeeds on `fW`'s lowering by the theorem. -/
theorem prepare_okT_w : ∃ vcp, Backend.prepare (vcOf fW) = .ok vcp :=
  Prep.prepare_okT dominated_w lowerScopeT_w lowerFunction_w

theorem prepare_ok_cfgT_w :
    ∃ vcp, Backend.prepare (vcOf fW) = .ok vcp ∧ ∃ ss ps, vcp.cfg = .ok (ss, ps) :=
  Prep.prepare_ok_cfgT dominated_w lowerScopeT_w lowerFunction_w

theorem prepIn_w : Prep.PrepIn (vcOf fW) := Prep.prepIn_of_lowerT dominated_w lowerScopeT_w lowerFunction_w

/-- **Witness** (integer specialization): `prepare_ok_viaT` on the subset-E `fInt`. -/
theorem prepare_ok_viaT_int : ∃ vcp, Backend.prepare (vcOf fInt) = .ok vcp := by
  have hok : (lowerFunction fInt).toBool = true := by native_decide
  unfold vcOf
  cases h : lowerFunction fInt with
  | error e => rw [h] at hok; cases hok
  | ok vc => exact Prep.prepare_ok_viaT (by native_decide) (by native_decide) h

theorem ctlInstsB_w : ctlInstsB (vcpOf fW) = true := by native_decide
theorem emitCondsB_w : emitCondsB (vcpOf fW) = true := by native_decide
theorem killFreeB_w : killFreeB (vcpOf fW) = true := by native_decide

/-- **Witness**: `ctlInstsB` decides `CtlInsts` of `fW`'s prepared code. -/
theorem ctlInsts_w : CtlInsts (vcpOf fW) := ctlInsts_of_ctlInstsB ctlInstsB_w

theorem formsCovered_w : FormsCovered default (vcpOf fW) := (formsCoveredB_iff _ _).mp (by native_decide)

theorem ctlSpill_w : ∀ vb ∈ (vcOf fW).blocks.toList, ∀ i ∈ vb.insts.toList, i.isCtl = true →
    SpillInstOk i := ctlSpill_of_ctlSpillB (by native_decide)

theorem resClass_w : ResClassOk fW := resClassOk_of_resClassOkB (by native_decide)
theorem arity_w : ArityOk fW := arityOk_of (by native_decide)
theorem tryArg_w : Compile.tryArgClassOk fW = true := by native_decide

/-- **Witness**: `lowerRFunc` lowers the spill allocation of `fW`'s prepared code by the
theorem. -/
theorem lowerRFunc_spillAllocT_w : ∃ af, lowerRFunc (vcpOf fW) (spillAlloc (vcpOf fW)) = .ok af :=
  lowerRFunc_spillAllocT dominated_w lowerScopeT_w arity_w tryArg_w resClass_w lowerFunction_w
    prepare_w ctlSpill_w formsCovered_w ctlInsts_w

theorem spillAccepted_w : AllocChecked (vcpOf fW) (spillAlloc (vcpOf fW)) :=
  spillAcceptedT dominated_w lowerScopeT_w arity_w tryArg_w resClass_w lowerFunction_w prepare_w
    ctlSpill_w formsCovered_w killFreeB_w

/-- **Witness**: the spill allocation's code of `fW` is ready by the theorem. -/
theorem emitReady_spill_of_w : emitReady (afOf fW) = true :=
  emitReady_spill_of (prepDomain_ofT dominated_w lowerScopeT_w lowerFunction_w) prepare_w
    spillAccepted_w formsCovered_w ctlInsts_w emitCondsB_w alloc_w

theorem lowerAlloc_of_spill_w : ∃ af, lowerAlloc (vcpOf fW) (.error "no allocator") = .ok af :=
  lowerAlloc_of_spill lowerRFunc_spillAllocT_w _

theorem lowerAllocReady_emit_of_w : ∃ af, lowerAllocReady (vcpOf fW) (.error "no allocator") = .ok af ∧
    ∃ fa fb, emitFunc 0 af = .ok fa ∧ fa.layout = .ok fb :=
  lowerAllocReady_emit_of lowerRFunc_spillAllocT_w
    (fun _ ha => emitReady_spill_of (prepDomain_ofT dominated_w lowerScopeT_w lowerFunction_w)
      prepare_w spillAccepted_w formsCovered_w ctlInsts_w emitCondsB_w ha) _ 0

/-- **Witness**: allocation, emission and layout of `fW` succeed by the theorem, with any
allocator answer. -/
theorem backend_total_emitT_w (ra : Except String RFunc) :
    AllocChecked (vcpOf fW) (allocResult (vcpOf fW) (readyAnswer (vcpOf fW) ra)) ∧
    ∃ af, lowerAllocReady (vcpOf fW) ra = .ok af ∧ ∃ fa fb, emitFunc 0 af = .ok fa ∧ fa.layout = .ok fb :=
  backend_total_emitT dominated_w lowerScopeT_w arity_w tryArg_w resClass_w lowerFunction_w prepare_w
    ctlSpill_w formsCovered_w killFreeB_w ctlInsts_w emitCondsB_w ra 0

/-- **Witness**: `fW` is in the typed scope `fnScopeTB` through the typed input scope. -/
theorem fnScopeTB_of_inT_w : fnScopeTB fW = true := fnScopeTB_of_inT fnScopeInTB_w functionE_w

/-- **Witness**: the compiler's pipeline compiles `fW`, for every allocator answer. -/
theorem pipeT_okT_w (o : Lean.Json) :
    ∃ a, pipeT fW 0 0 o = .ok a ∧ lowerCheckT fW a.vc = true ∧ prepCheck a.vc a.vcp = true ∧
      AllocChecked a.vcp a.rf ∧ FormsCovered ⟨a.fa.k, a.af.slotBase⟩ a.vcp :=
  pipeT_okT fnScopeInTB_w 0 0 o

/-- **Witness** (integer inclusion): `fInt` is in both input scopes. -/
theorem fnScopeInTB_int : fnScopeInTB fInt = true := fnScopeInTB_of_fnScopeInB (by native_decide)
theorem fnScopeInB_int : fnScopeInB fInt = true := fnScopeInB_of_fnScopeInTB fnScopeInTB_int (by native_decide)
theorem lowerScopeB_int : lowerScopeB fInt = true :=
  lowerScopeB_of_lowerScopeTB lowerScopeTB_int (by native_decide)

/-- `fW`'s CLIF text. -/
def srcW : String := "function %w(i64, i8) -> i64 {
block0(v0: i64, v1: i8):
    v2 = load.f64 v0
    v3 = f64const 0x1.0p-2
    v4 = select v1, v2, v3
    store v4, v0+8
    v5 = bitcast.i64 v4
    return v5
}
"

/-- `fInt`'s CLIF text. -/
def srcInt : String := "function %i(i64, i64) -> i64 {
block0(v0: i64, v1: i64):
    v2 = iadd v0, v1
    return v2
}
"

/-- A one-function crate of `fW`'s CLIF text. -/
def crateW : LinkInput :=
  { funcs := [{ clif := srcW, ra := "" }], addrs := [], syms := [], raStar := 0, D := 0 }

/-- A one-function crate of `fInt`'s CLIF text. -/
def crateInt : LinkInput :=
  { funcs := [{ clif := srcInt, ra := "" }], addrs := [], syms := [], raStar := 0, D := 0 }

#guard crateW.prog.funcs.map Compile.functionE == [false] && !InScopeIn crateW

theorem inScopeInT_w : InScopeInT crateW = true := by native_decide
theorem inScopeIn_int : InScopeIn crateInt = true := by native_decide

/-- **Witness**: every function of the float crate compiles. -/
theorem resultsT_ok_inT_w : crateW.resultsT.all (·.2.toBool) = true := resultsT_ok_inT inScopeInT_w

/-- **Witness** (integer): `InScopeIn` → `InScopeInT`, and the integer crate compiles. -/
theorem inScopeInT_int : InScopeInT crateInt = true := inScopeInT_of_inScopeIn inScopeIn_int
theorem resultsT_ok_input_int : crateInt.resultsT.all (·.2.toBool) = true :=
  resultsT_ok_input inScopeIn_int

end FloatTotalT
