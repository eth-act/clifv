from pathlib import Path
p=Path('/tmp/stock-div-next-staged/FV/E2E/StockMixedDivWitness.lean');s=p.read_text();a=s.index('private def grid : Bool');b=s.index('-- witness: native_decide',a)
pre='''/-- Concrete original inputs used only to witness actual source outcomes. -/
private def caseInput (config : Configuration) (positive : Bool) : Nat → BitVec (valueType config).width :=
  fun i => BitVec.ofNat _ (if positive then 2*i+1 else 0)

private def caseWanted (config : Configuration) (op : Clif.DivOp) (safe positive : Bool) :=
  let input := caseInput config positive
  Clif.Sem.div op (StockHighMulNIWitness.resultValue config input) (if safe then 2 else input 8)

private def caseRun (config : Configuration) (op : Clif.DivOp) (safe positive : Bool) : Clif.Outcome :=
  Clif.runLoop Clif.Env.empty {funcs := []} 250
    ⟨frame config op safe (caseInput config positive) 4096,[],Clif.Mem.empty⟩

private def outcomeAgrees (ty : Clif.Ty) (wanted : Except Clif.TrapCode (BitVec ty.width))
    (actual : Clif.Outcome) : Bool :=
  match wanted,actual with
  | .error code,.trapped observed => code == observed
  | .ok bits,.returned vals _ => decide (vals = [⟨ty,bits⟩])
  | _,_ => false

private def sourceCases (config : Configuration) (op : Clif.DivOp) (safe : Bool) : Bool :=
  outcomeAgrees (valueType config) (caseWanted config op safe false) (caseRun config op safe false) &&
  outcomeAgrees (valueType config) (caseWanted config op safe true) (caseRun config op safe true)

private theorem outcomeAgrees_sound {ty : Clif.Ty}
    {wanted : Except Clif.TrapCode (BitVec ty.width)} {actual : Clif.Outcome}
    (checked : outcomeAgrees ty wanted actual = true) :
    match wanted with
    | .error code => actual = .trapped code
    | .ok bits => ∃ mem,actual = .returned [⟨ty,bits⟩] mem := by
  cases wanted <;> cases actual <;> simp_all [outcomeAgrees]

private def grid : Bool := configurations.all fun config => operations.all fun op =>
  [false,true].all fun safe => sourceCases config op safe && checks config op safe false && checks config op safe true
'''
s=s[:a]+pre+s[b:];s=s.replace('| false => exact both.1\n    | true => exact both.2','| false => exact both.1.2\n    | true => exact both.2',1)
pos=s.index('/-- Actual checked/allocated/emitted artifacts')
extra='''/-- Actual source returns/traps inhabit the universal domain and all live
prefix families. These are fixed witness inputs; the source domain is arbitrary. -/
theorem source_cases (config : Configuration) (op : Clif.DivOp) (safe positive : Bool) :
    match caseWanted config op safe positive with
    | .error code => caseRun config op safe positive = .trapped code
    | .ok bits => ∃ mem,caseRun config op safe positive = .returned [⟨valueType config,bits⟩] mem := by
  have h := List.all_eq_true.mp checks_true config (by cases config <;> simp [configurations])
  have h := List.all_eq_true.mp h op (by cases op <;> simp [operations])
  have h := List.all_eq_true.mp h safe (by cases safe <;> simp)
  simp only [Bool.and_eq_true] at h
  have casesOk := h.1.1
  simp only [sourceCases,Bool.and_eq_true] at casesOk
  apply outcomeAgrees_sound
  cases positive with
  | false => exact casesOk.1
  | true => exact casesOk.2

'''
s=s[:pos]+extra+s[pos:];p.write_text(s);Path('/tmp/stock-div-next-staged/witness-status.txt').write_text('Prepared96 complete pipeline witnesses +96 exact original-source observations, arbitrary-entry fixture, outcome-observer soundness. Not compiled/applied yet. Universal mixed Domain/classifier separately compile Std3. No current-source edits.\n');print('Staged complete fixed source outcomes alongside pipeline witnesses; validation pending')
