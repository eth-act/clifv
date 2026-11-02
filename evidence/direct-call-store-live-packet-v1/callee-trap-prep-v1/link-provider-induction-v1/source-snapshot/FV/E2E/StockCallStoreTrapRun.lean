import FV.E2E.StockCallStoreTrapReady
import FV.E2E.StockCallStoreTrapTail
import FV.E2E.DeadCleanupTrapCall

namespace Backend.Stock.CallStore
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

private theorem seqRun_eq_on {sem sem' : Sem} :
    ∀ code : List MInst,(∀ inst ∈ code,sem inst = sem' inst) →
      ∀ values world,seqRun sem code values world = seqRun sem' code values world := by
  intro code
  induction code with
  | nil => intro _ _ _; rfl
  | cons inst rest ih =>
    intro same values world
    have head := same inst (List.mem_cons_self)
    have tail := ih (fun next member => same next (List.mem_cons_of_mem inst member))
    simp only [seqRun,head,tail]

/-- The old trapping-callee contract supplies xrT at the actual original call arguments. -/
theorem TrapReady.execute {f : Clif.Function} {result : Stock.Result} {env : Clif.Env}
    {cp : Clif.Program} {fr : Clif.Frame} {cm : Clif.Mem} {Γ : Rel} {fc : FnCtx}
    {X : ExtSem} {initial : Arm.ArmState} {trap : Clif.TrapCode}
    (source : TrapReady f result env cp fr cm Γ fc X initial trap)
    {args : List Clif.Val} (types : args.map (·.ty) = f.sig.params.map (·.ty))
    (arguments : ArgsAtEntry Γ.F f.sig args initial) {c : BitVec 64}
    (memory : RelW Γ f c fr.slots cm initial)
    (traps : XTrapsOk env (f.externs.map (·.2)) (indSigs f) (RelW Γ f c) X) :
    ∃ before,
      VUnwinds result.code
        (valueSemU Γ.F fc X (xrT (TrapCallSem env (f.externs.map (·.2)) (indSigs f) (RelW Γ f c) X trap)))
        (xrT (TrapCallSem env (f.externs.map (·.2)) (indSigs f) (RelW Γ f c) X trap)) source.seed initial 0 before ∧
      RelW Γ f c fr.slots cm before ∧ SameWorld Γ.F before initial := by
  obtain ⟨_,before,preRun,related⟩ := ABIReadOnly.seqRun_fall_realize types arguments (SameWorld.refl Γ.F initial)
    (b := 0) (start := 0) (by simpa only [Nat.zero_add] using source.reads) (fun _ => rfl) source.preRun
  have beforeMemory := mrStable_relW Γ f c fr.slots cm initial before (SameWorld.nf related) memory
  have noReturn := traps.1 source.ext source.member source.callee fr.slots cm before
    (some source.ext.name) [source.values source.argument] [source.values source.argument]
    [⟨.i64,source.liveWord⟩] trap source.found (Or.inl ⟨rfl,rfl⟩)
    (source.arguments before) beforeMemory source.sourceTrapped
  have trappedCall : TrapCallSem env (f.externs.map (·.2)) (indSigs f) (RelW Γ f c) X trap
      (some source.ext.name) [source.values source.argument] before :=
    ⟨noReturn,.inl ⟨source.ext,source.member,source.callee,fr.slots,cm,
      [source.values source.argument],[⟨.i64,source.liveWord⟩],source.found,
      .inl ⟨rfl,rfl⟩,source.arguments before,beforeMemory,source.sourceTrapped⟩⟩
  let XT := TrapCallSem env (f.externs.map (·.2)) (indSigs f) (RelW Γ f c) X trap
  have preRunU : seqRun (valueSemU Γ.F fc X (xrT XT)) source.prelude source.seed initial =
      some (.fall source.values before) := by
    rw [seqRun_eq_on source.prelude ?_]
    · exact preRun
    · intro inst member
      obtain ⟨j,found⟩ := List.mem_iff_getElem?.mp member
      have checked := source.reads j inst found
      apply valueSemU_of_not_call
      · intro info equal
        subst inst
        simp [Backend.ABIReadOnly.instruction,pureNoFlags,pureForm] at checked
      · intro info ti equal
        subst inst
        simp [Backend.ABIReadOnly.instruction,pureNoFlags,pureForm] at checked
  refine ⟨before,?_,beforeMemory,related⟩
  apply trap_call_tail source.placed (info := ⟨.sym source.ext.name,
    retPairs [(source.argument,.x 0)],callDefs [(.x 0,source.called)]⟩)
    (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using source.code) preRunU
    (operands_call_sym source.ext.name [(source.argument,.x 0)] [(.x 0,source.called)])
  simpa only [callDest,vuses_call,List.map_cons,List.map_nil] using (xrT_of trappedCall)

end Backend.Stock.CallStore
