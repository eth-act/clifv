import FV.E2E.StockMemoryPairedStutterValue
import FV.Backend.Proof.StockAcquirePendingValues

namespace E2E.StockAcquirePending
open Backend.DeadCleanup
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- Both worlds retain the same complete capture history and required value relation. -/
def PairedPendingScanRel (f : Clif.Function) (result : Result) (ctx : Ctx) (bi : Nat)
    (env : Clif.Env) (cp : Clif.Program) (Γ : Rel) (c : BitVec 64) (D : BitVec 64 → Prop)
    (snapshots : List (SunkReadSnapshot ctx env cp)) (st : State) (s : SourcePoint)
    (regs : Nat → CV) (worlds : W2) : Prop :=
  PendingGuardedScanRel f result ctx bi env cp (RelW Γ f c) snapshots st s regs worlds.1 ∧
  PendingGuardedScanRel f result ctx bi env cp (RelW Γ f c) snapshots st s regs worlds.2 ∧
  SameWorld (Zof Γ.F D s.2.2) worlds.1 worlds.2

/-- The empty history preserves the existing paired relation exactly. -/
theorem paired_pending_nil {f : Clif.Function} {result : Result} {ctx : Ctx} {bi : Nat}
    {env : Clif.Env} {cp : Clif.Program} {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop}
    {st : State} {s : SourcePoint} {regs : Nat → CV} {worlds : W2} :
    PairedPendingScanRel f result ctx bi env cp Γ c D [] st s regs worlds ↔
      StockMemory.PairedScanRel f result ctx bi Γ c D st s regs worlds := by
  simp only [PairedPendingScanRel,StockMemory.PairedScanRel,pending_guarded_nil]

/-- Existing guarded lockstep lifts internal one-world family proofs to paired execution.
The successful source step preserves memory. Fault branches remain separate. -/
theorem paired_pending_scan_of_guarded_stutter_value {f : Clif.Function} {result : Result} {ctx : Ctx}
    {bi : Nat} {record : ScanRecord} {env : Clif.Env} {cp : Clif.Program}
    {snapshots : List (SunkReadSnapshot ctx env cp)}
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (single : ∀ Rd : BitVec 64 → Prop,
      ScanFallRefines (IndexedSourceInst env cp f ctx bi)
        (valueSemG Γ.F fc X Rd Γ.syms [] [] 0 (fun _ _ _ _ => False)) result.final.alias
        (PendingGuardedScanRel f result ctx bi env cp (RelW Γ f c) snapshots) record)
    (stutter : ∀ s s',IndexedSourceInst env cp f ctx bi record.inst s s' → s'.2.2 = s.2.2)
    (tls : XTls Γ.F X) :
    ScanFallRefines (IndexedSourceInst env cp f ctx bi) (pairSem (valueSem Γ.F fc X))
      result.final.alias (PairedPendingScanRel f result ctx bi env cp Γ c D snapshots) record := by
  intro s s' sourceIndex ρ q before
  obtain ⟨firstHeld,secondHeld,worlds⟩ := before
  obtain ⟨ρ1,w1,first,post1⟩ := single (fun a => ¬ Zof Γ.F D s.2.2 a) s s' sourceIndex ρ q.1 firstHeld
  obtain ⟨ρ2,w2,second,post2⟩ := single (fun a => ¬ Zof Γ.F D s.2.2 a) s s' sourceIndex ρ q.2 secondHeld
  let code := record.output.emitted.toList.map (·.mapRegs
    (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))
  obtain ⟨w2',equal,paired,related⟩ := pair_fall
    (fun _ _ _ _ h => valueSemG_sub h)
    (guardedStep0_value (D := D) (syms := Γ.syms) tls fc s.2.2 code [] []) worlds first second
  obtain ⟨sameRegs,sameWorld⟩ := SeqEnd.fall.inj equal
  subst ρ2
  subst w2'
  refine ⟨ρ1,(w1,w2),paired,post1,post2,?_⟩
  rwa [stutter s s' sourceIndex]

end E2E.StockAcquirePending
