import FV.Backend.Proof.StockCmpMatchedZero
import FV.Backend.Proof.StockCmpMatchedRegister
import FV.Backend.Proof.StockCmpMatchedImmediate
namespace Backend.Stock.Proof.ScalarCmp.MatchedWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarCmp
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private instance : DecidableEq V := fun a b => decidable_of_iff ((a == b) = true) beq_iff_eq
private def fixture : Clif.Function := {
  name := "stock_cmp_actual_match_witness"
  sig := {params := [⟨.i8,.none,.normal⟩,⟨.i8,.none,.normal⟩,⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩],returns := [⟨.i8,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i8),(31,.i8),(8,.i64),(32,.i64)],body := [
    ⟨[63],.iconst .i8 (3#8)⟩,⟨[70],.iconst .i8 (0#8)⟩,
    ⟨[100],.icmp .eq .i8 7 70⟩,⟨[101],.icmp .ult .i8 7 63⟩,
    ⟨[102],.icmp .slt .i8 7 31⟩,⟨[103],.icmp .eq .i64 8 32⟩,
    ⟨[104],.binary .band .i8 100 101⟩,⟨[105],.binary .band .i8 104 102⟩,
    ⟨[106],.binary .band .i8 105 103⟩],term := .ret [106]}] }
private def built : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx fixture).toOption.getD (sinkCtx,#[],sinkState)
private abbrev ctx := built.1
private abbrev st := built.2.2
private def zeroEnv : Isle.Interp.Env V := #[some (.value 7)]
private def wideEnv : Isle.Interp.Env V := #[some (.data 145 (ccIdx .eq) []),some (.value 8),some (.ty (.int 64)),some (.value 32)]
private def narrowEnv : Isle.Interp.Env V := #[some (.data 145 (ccIdx .slt) []),some (.value 7),some (.ty (.int 8)),some (.value 31)]
private def immediateEnv : Isle.Interp.Env V := #[some (.data 145 (ccIdx .ult) []),some (.ty (.int 8)),some (.value 7),some (.op (.imm12 ⟨3,false⟩))]
private def ZeroMatched : Prop :=
  (matchRule program (Stock.sem ctx) {} 40 (cmpZeroRule false false)
    [.data 145 (ccIdx .eq) [],.value 7,.value 70]).run (st,#[]) = .ok (some zeroEnv,st,#[])
private def WideMatched : Prop :=
  (matchRule program (Stock.sem ctx) {} 40 rule_inst_5128
    [.data 145 (ccIdx .eq) [],.value 8,.value 32]).run (st,#[]) = .ok (some wideEnv,st,#[])
private def NarrowMatched : Prop :=
  (matchRule program (Stock.sem ctx) {} 40 rule_inst_5108
    [.data 145 (ccIdx .slt) [],.value 7,.value 31]).run (st,#[]) = .ok (some narrowEnv,st,#[])
private def ImmediateMatched : Prop :=
  (matchRule program (Stock.sem ctx) {} 40 rule_inst_5134
    [.data 145 (ccIdx .ult) [],.value 7,.value 63]).run (st,#[]) = .ok (some immediateEnv,st,#[])
private theorem scope : LowerScope fixture := lowerScope_of (by decide +kernel)
private theorem build : Stock.buildCtx fixture = .ok built := by rfl
section Kernel
attribute [local semireducible] Isle.Aarch64.program
private theorem zero_matched : ZeroMatched := by unfold ZeroMatched; rfl
private theorem wide_matched : WideMatched := by unfold WideMatched; rfl
private theorem narrow_matched : NarrowMatched := by unfold NarrowMatched; rfl
private theorem immediate_matched : ImmediateMatched := by unfold ImmediateMatched; rfl
private theorem lowered : (Stock.lower fixture).toOption.isSome = true := by decide +kernel
end Kernel
/-- A complete original Stock driver run contains all four comparison source
forms; actual matching in its built context inhabits each observation theorem. -/
theorem stock_cmp_match_observations_witness :
    ∃ result,Stock.lower fixture = .ok result ∧ LowerScope fixture ∧ MappedCtxInv fixture ctx ∧
      ZeroMatched ∧ WideMatched ∧ NarrowMatched ∧ ImmediateMatched ∧
      (∃ j info literal,ctx.defInst? 70 = some j ∧ ctx.insts[j]? = some info ∧
        info.data = .data 152 35 [.data 151 57 [],.int literal] ∧ u64 literal = 0) ∧
      (∃ j info literal imm,ctx.defInst? 63 = some j ∧ ctx.insts[j]? = some info ∧
        info.data = .data 152 35 [.data 151 57 [],.int literal] ∧ Imm12.ofNat? (u64 literal) = some imm) := by
  have inv := buildCtx_mappedInv scope build
  have hz := zero_matched
  have hw := wide_matched
  have hn := narrow_matched
  have hi := immediate_matched
  unfold ZeroMatched at hz
  unfold WideMatched at hw
  unfold NarrowMatched at hn
  unfold ImmediateMatched at hi
  obtain ⟨zj,zi,zl,_,zdef,zfound,zdata,zvalue,_,_⟩ := stock_cmp_zero_match_observed data_program ctx inv false false .eq 7 70 hz
  have wide := stock_cmp_wide_match_observed data_program ctx .eq .size64 (by rfl) hw
  have narrow := stock_cmp_narrow_match_observed data_program ctx .slt false true (by rfl) hn
  obtain ⟨ij,ii,il,imm,idef,ifound,idata,encoded,_,_,_⟩ :=
    stock_cmp_immediate_match_observed data_program ctx inv true .ult .i8 7 63 (by rfl) hi
  have actual := lowered
  cases run : Stock.lower fixture with
  | error err =>
    rw [run] at actual
    simp only [Except.toOption,Option.isSome_none,Bool.false_eq_true] at actual
  | ok result =>
    exact ⟨result,rfl,scope,inv,zero_matched,wide_matched,narrow_matched,immediate_matched,
      ⟨zj,zi,zl,zdef,zfound,zdata,zvalue⟩,⟨ij,ii,il,imm,idef,ifound,idata,encoded⟩⟩
end Backend.Stock.Proof.ScalarCmp.MatchedWitness
