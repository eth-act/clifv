module

public import FV.Backend.RegallocPerEdgePrepare
public import FV.Backend.Proof.PrepareCheck

@[expose] public section

/-! Structural preparation relation for actual per-successor copies. This
internal check is separate from the original check and source input conditions.
Completeness for actual prepareAt is a separate universal proof obligation. -/
namespace Backend.Proof.PerEdgePrep
open Backend Backend.Proof.Driver

def edgeBlockOkAt (vc : VCode) (succs : Array (Array Nat)) (block target : Nat) : Bool :=
  match vc.blocks[block]? with
  | some b =>
    (match b.insts.toList with | [.jump _] => true | _ => false) &&
    decide (b.params = #[]) && decide (succs[block]? = some #[target])
  | none => false

def keptOkAt (vc vcp : VCode) (edges edges' : Array (Array (Array Reg)))
    (ss ss' : Array (Array Nat)) (b b' : Nat) : Bool :=
  match vc.blocks[b]?,vcp.blocks[b']? with
  | some vb,some vb' =>
    decide (vb'.params = vb.params) && decide (vb'.branchArgs = vb.branchArgs) &&
    decide (vb'.insts.size = vb.insts.size) && decide (vb'.insts.pop = vb.insts.pop) &&
    lastOk vb vb' &&
    (match ss[b]?,ss'[b']? with
      | some sb,some sb' => decide (sb'.size = sb.size) && (List.range sb.size).all fun j =>
        match sb[j]?,sb'[j]? with
        | some s,some t => match sigmaOf vc vcp s with
          | some s' =>
            (decide (t = s') && decide ((edges'[b']?.bind (·[j]?)) = edges[b]?.bind (·[j]?))) ||
            (decide ((edges'[b']?.bind (·[j]?)) = some #[]) && edgeBlockOkAt vcp ss' t s' &&
              decide ((edges'[t]?.bind (·[0]?)) = edges[b]?.bind (·[j]?)))
          | none => false
        | _,_ => false
      | _,_ => false)
  | _,_ => false

def prepCheckAt (vc : VCode) (edges : Array (Array (Array Reg))) (prepared : EdgeVCode) : Bool :=
  let vcp := prepared.code
  match vc.cfg,vcp.cfg with
  | .ok (ss,_),.ok (ss',_) =>
    decide (sigmaOf vc vcp 0 = some 0) && liveOf ss 0 &&
    ((List.range vc.blocks.size).all fun b => !liveOf ss b || match sigmaOf vc vcp b with
      | none => false
      | some b' => keptOkAt vc vcp edges prepared.edges ss ss' b b' &&
          (ss[b]?.getD #[]).all fun s => decide (s < vc.blocks.size) && liveOf ss s) &&
    (((vc.hasTryCall || !vcp.hasTryCall) && (vc.hasTls || !vcp.hasTls)) && vcp.outgoing == vc.outgoing)
  | _,_ => false
end Backend.Proof.PerEdgePrep

namespace Backend
/-- Internal preparation check. Successful callers receive the exact indexed
structural relation; completeness under original inputs is proved separately. -/
def prepareCheckedAt (vc : VCode) (edges : Array (Array (Array Reg))) : Except String EdgeVCode := do
  let prepared ← prepareAt vc edges
  if !(Proof.PerEdgePrep.prepCheckAt vc edges prepared) then
    throw "indexed preparation relation rejected"
  pure prepared
end Backend
