module

public import FV.Backend.Proof.IselCmpDiv
public import FV.Backend.Proof.StockDivAliasSem
public import FV.Backend.Proof.StockDivImmValues
public import FV.Backend.Proof.StockAliasTerminal

@[expose] public section

namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private theorem alias_fresh {aliases : Array (Option Nat)} {lo n : Nat}
    (bound : aliases.size ≤ lo) (fresh : lo ≤ n) : aliasNum aliases n = n := by
  apply chaseF_none
  rw [Array.getElem?_eq_none (by omega)]
  rfl
private theorem alias_renaming (a : Array (Option Nat)) :
    VRenaming (Backend.lowerFunction.resolve a (a.size+1)) (aliasNum a) := by
  refine ⟨fun n c => resolve_vreg a _ n c,?_⟩
  intro r hr
  cases r with
  | vreg n c => exact False.elim (hr n c rfl)
  | _ => simp [Backend.lowerFunction.resolve]
private theorem renamed_defs (a : Array (Option Nat)) (m : MInst) :
    vdefs (m.mapRegs (Backend.lowerFunction.resolve a (a.size+1))) = (vdefs m).map (aliasNum a) := by
  unfold vdefs
  rw [operands_mapRegs (alias_renaming a)]
  cases actual : m.operands with
  | error err => rfl
  | ok ops =>
    simp only [Except.map,Array.toList_map]
    rw [filter_map_rn _ Operand.isDef (fun _ => rfl)]
    simp only [List.map_map]
    rfl
/-- Real Stock constant materialization executes through final aliases under
any refining machine semantics. Alias idempotence is an internal driver invariant;
semantic invariance is derived, rather than added as a caller assumption. -/
theorem stock_div_imm_resolved {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {w e : Nat}
    (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (extension : e = 0 ∨ e = 1)
    {i : Int} {st next : State} {tr trace : Array RuleId} {n : Nat} {out : V}
    (run : (applyTerm p (Stock.sem ctx) cfg (n+40) 27 553 (immArgs w e i)).run (st,tr) = .ok (some out,next,trace))
    {aliases : Array (Option Nat)} (bounded : aliases.size ≤ st.base.nextVreg)
    (idem : ∀ k,aliasNum aliases (aliasNum aliases k) = aliasNum aliases k) :
    ∃ ms d,next = {st with base := next.base} ∧ out = .reg (.vreg d .int) ∧
      CodeShape st.base next.base ms d st.base.nextVreg ∧ d < next.base.nextVreg ∧
      ∀ ρ,∃ ρ' X,PRun F isem (ms.map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
        lo64 (ρ' d) = BitVec.ofNat 64 X ∧ X % 2^w = u64 i % 2^w ∧
        (w ≠ 32 ∨ e = 0 ∨ u64 i < 2^32 → X = immVal w (e == 0) (u64 i)) ∧
        ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k := by
  have mappedRefines := stock_div_alias_sem_refines refines aliases
  obtain ⟨frame,ms,d,output,shape,values⟩ := stock_div_imm_values hp ctx hc mappedRefines width extension run
  obtain ⟨d',ms',same,_,bound,_⟩ := immOut_lt (by omega) (by omega) Arm.ArmState.default
    (show ImmOut F (aliasSem aliases isem) w e (u64 i) st.base next.base out from ⟨ms,d,output,shape,values⟩)
  have resultEq : d = d' := (Reg.vreg.inj (V.reg.inj (output.symm.trans same))).1
  rw [← resultEq] at bound
  refine ⟨ms,d,frame,output,shape,bound,?_⟩
  intro ρ
  obtain ⟨raw,X,execution,value,modulo,extended⟩ := values (fun k => ρ (aliasNum aliases k))
  obtain ⟨ρ',mapped,agree,_⟩ := stock_alias_fresh_prun bounded
    (fun m member k defined => (shape.defs m member k defined).1)
    (fun m member k used => by rcases shape.uses m member k used with fresh | rfl; exact fresh; exact Nat.le_refl _)
    (stock_div_alias_sem_invariant aliases idem isem) execution
  have actual : PRun F isem (ms.map (·.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' := by
    intro world
    obtain ⟨nextWorld,exec,kept⟩ := mapped world
    rw [stock_div_alias_sem_run aliases idem isem ms ρ world] at exec
    exact ⟨nextWorld,exec,kept⟩
  have defs : ∀ m ∈ ms.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))),
      ∀ k ∈ vdefs m,st.base.nextVreg ≤ k ∧ k < next.base.nextVreg := by
    intro m member k defined
    obtain ⟨original,rawMember,rfl⟩ := List.mem_map.mp member
    rw [renamed_defs] at defined
    obtain ⟨key,rawDefined,rfl⟩ := List.mem_map.mp defined
    rw [alias_fresh bounded (shape.defs original rawMember key rawDefined).1]
    exact shape.defs original rawMember key rawDefined
  refine ⟨ρ',X,actual,?_,modulo,extended,?_⟩
  · rw [agree d shape.res]; exact value
  · intro k outside
    obtain ⟨nextWorld,exec,_⟩ := actual Arm.ArmState.default
    exact seqRun_fall_frame (fun m member defined => by have := defs m member k defined; omega) exec
/-- Actual successful driver aliases supply the idempotence invariant used
above under the preserved original scope/dominance conditions. -/
theorem stock_div_driver_alias_idem {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f) :
    ∀ k,aliasNum result.final.alias (aliasNum result.final.alias k) = aliasNum result.final.alias k :=
  stock_lower_alias_idempotent run scope dominated
end Backend.Stock.Proof.ScalarDiv
