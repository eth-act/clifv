import FV.Backend.RegallocOps

/-!
# The `prepare` validator (M7): `prepCheck vc vcp`

An executable check, run after `prepare vc = .ok vcp`, whose acceptance implies that `vcp`
simulates `vc` (`PrepareSound.lean`: VCode returns and traps of `vc` are returns and traps of
`vcp`). It checks the relation `prepare` establishes, block by block, instead of `prepare`'s
loops (reachability worklist, critical-edge splitting, the fuel-bounded reverse postorder):

* the live blocks of `vc` (`liveOf`: those `reachable` from the entry, which `prepare` keeps;
  untrusted, the check only needs the entry to be live and live blocks' successors to be live
  blocks of `vc`) have a counterpart `σ b` in `vcp` (the block with the same label) with the
  same parameters, branch arguments and instructions, except that the last instruction may be
  retargeted (`MInst.setTargets`);
* the entry block is its own counterpart (`σ 0 = 0`);
* every successor `s` of a live block has a counterpart, and successor `j` of `σ b`
  is `σ s` or an edge block (`jump`, no parameters, no branch arguments) whose successor is
  `σ s`; the latter only for a block without branch arguments.

Blocks of `vc` that are not live (the unreachable ones `prepare` drops) are never reached, and
are not checked: their labels may be reused by `prepare`'s edge blocks.
-/

namespace Backend.Proof.Driver

open Backend

/-- The counterpart in `vcp` of block `b` of `vc`: the block with the same label. -/
def sigmaOf (vc vcp : VCode) (b : Nat) : Option Nat :=
  match vc.blocks[b]? with
  | some vb => vcp.blocks.findIdx? (·.label == vb.label)
  | none => none

/-- `t` is an edge block of `vcp` (`jump`, no parameters, no branch arguments) whose only
successor is `s'`. -/
def edgeBlockOk (vcp : VCode) (ss' : Array (Array Nat)) (t s' : Nat) : Bool :=
  match vcp.blocks[t]? with
  | some eb =>
    (match eb.insts.toList with
      | [.jump _] => true
      | _ => false) &&
    decide (eb.params = #[]) && decide (eb.branchArgs = #[]) && decide (ss'[t]? = some #[s'])
  | none => false

/-- The last instruction of `vb'` is that of `vb`, possibly retargeted. -/
def lastOk (vb vb' : VBlock) : Bool :=
  match vb.insts.back?, vb'.insts.back? with
  | some i, some i' => decide (i' = i) || decide (i.setTargets i'.targets = some i')
  | none, none => true
  | _, _ => false

/-- Block `b` of `vc` and its counterpart `b'` in `vcp`. -/
def keptOk (vc vcp : VCode) (ss ss' : Array (Array Nat)) (b b' : Nat) : Bool :=
  match vc.blocks[b]?, vcp.blocks[b']? with
  | some vb, some vb' =>
    decide (vb'.params = vb.params) && decide (vb'.branchArgs = vb.branchArgs) &&
    decide (vb'.insts.size = vb.insts.size) && decide (vb'.insts.pop = vb.insts.pop) &&
    lastOk vb vb' &&
    (match ss[b]?, ss'[b']? with
      | some sb, some sb' => decide (sb'.size = sb.size) && (List.range sb.size).all fun j =>
        match sb[j]?, sb'[j]? with
        | some s, some t => match sigmaOf vc vcp s with
          | none => false
          | some s' => decide (t = s') ||
              (decide (vb.branchArgs = #[]) && edgeBlockOk vcp ss' t s')
        | _, _ => false
      | _, _ => false)
  | _, _ => false

/-- Block `b` is reachable from the entry (`reachable`, as in `prepare`). -/
def liveOf (ss : Array (Array Nat)) (b : Nat) : Bool := (reachable ss)[b]?.getD false

/-- **The `prepare` validator.** -/
def prepCheck (vc vcp : VCode) : Bool :=
  match vc.cfg, vcp.cfg with
  | .ok (ss, _), .ok (ss', _) =>
    decide (sigmaOf vc vcp 0 = some 0) && liveOf ss 0 &&
    ((List.range vc.blocks.size).all fun b => !liveOf ss b || match sigmaOf vc vcp b with
      | none => false
      | some b' => keptOk vc vcp ss ss' b b' &&
          (ss[b]?.getD #[]).all fun s => decide (s < vc.blocks.size) && liveOf ss s) &&
    -- no `tryCall` appears (`prepare` keeps and retargets the instructions)
    (vc.hasTryCall || !vcp.hasTryCall)
  | _, _ => false

end Backend.Proof.Driver
