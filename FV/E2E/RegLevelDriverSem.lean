import FV.Backend.Proof.RegallocCSem
import FV.Backend.Proof.CSemRename
import FV.Backend.Proof.LowerRename
import FV.Backend.Proof.IselContract
import FV.Backend.Proof.LowerContract

/-!
# The driver's facts about `csem` (M6: `DriverSem`, `CallsRefine`)

* `driverSem_csem`: `Args` reads the world's argument registers, `jump` is `goto 0`, `csem` does
  not depend on vreg names (`rename`: the canonical allocation replaces every vreg) nor on branch
  labels (`retarget`).
* `callsRefine_csem`: the callee contract at the VCode level from the contract `XCallsOk` of the
  external semantics `X` (a call of an extern returns the extern's results and a related world).
-/

namespace Backend.Proof

open Backend Backend.Proof.Driver

/-! ## Renaming -/

theorem amode_visit_mapRegs {m : Type → Type} [Monad m] [LawfulMonad m] (f : OpSpec → Reg → m Reg)
    (g : Reg → Reg) (am : AMode) :
    AMode.visit f (am.mapRegs g) = AMode.visit (fun sp r => f sp (g r)) am := by
  cases am <;> rfl

theorem condBrKind_visit_mapRegs {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : OpSpec → Reg → m Reg) (g : Reg → Reg) (k : CondBrKind) :
    CondBrKind.visit f (k.mapRegs g) = CondBrKind.visit (fun sp r => f sp (g r)) k := by
  cases k <;> rfl

/-- Visiting a renamed instruction is visiting the instruction with the renaming applied first. -/
theorem visit_mapRegs {m : Type → Type} [Monad m] [LawfulMonad m] (f : OpSpec → Reg → m Reg)
    (g : Reg → Reg) (i : MInst) :
    MInst.visitOperands f (i.mapRegs g) = MInst.visitOperands (fun sp r => f sp (g r)) i := by
  cases i with
  | call info =>
    obtain ⟨dest, uses, defs⟩ := info
    cases dest <;> simp [MInst.visitOperands, MInst.mapRegs, List.mapM_map, Function.comp_def]
  | tryCall info ti =>
    obtain ⟨dest, uses, defs⟩ := info
    cases dest <;> simp [MInst.visitOperands, MInst.mapRegs, List.mapM_map, Function.comp_def]
  | args ds => simp [MInst.visitOperands, MInst.mapRegs, List.mapM_map, Function.comp_def]
  | rets us => simp [MInst.visitOperands, MInst.mapRegs, List.mapM_map, Function.comp_def]
  | _ =>
    simp only [MInst.visitOperands, MInst.mapRegs, amode_visit_mapRegs, condBrKind_visit_mapRegs]

theorem assign_mapRegs {g : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming g gn) (i : MInst)
    (regs : Array Reg) : (i.mapRegs g).assign regs = i.assign regs := by
  unfold MInst.assign
  dsimp only
  rw [visit_mapRegs]
  congr 4
  funext sp r
  cases r with
  | vreg n c => rw [hg.vreg]
  | x n => rw [hg.real _ (fun _ _ h => by cases h)]
  | v n => rw [hg.real _ (fun _ _ h => by cases h)]
  | xzr => rw [hg.real _ (fun _ _ h => by cases h)]
  | sp => rw [hg.real _ (fun _ _ h => by cases h)]

theorem canonBase_rn (gn : Nat → Nat) (ops : Array Operand) (k : Nat) :
    canonBase (ops.map (rnOp gn)) k = canonBase ops k := by
  unfold canonBase
  rw [Array.getElem?_map]
  cases ops[k]? with
  | none => rfl
  | some o =>
    obtain ⟨v, c, kd, p, con⟩ := o
    simp only [Option.map, rnOp]
    cases con <;> cases c <;> rfl

theorem canonRegs_rn (gn : Nat → Nat) (ops : Array Operand) :
    canonRegs (ops.map (rnOp gn)) = canonRegs ops := by
  unfold canonRegs canonReg
  simp only [Array.size_map, Array.getElem?_map, canonBase_rn]
  congr 1
  apply List.map_congr_left
  intro k _
  cases ops[k]? with
  | none => rfl
  | some o =>
    obtain ⟨v, c, kd, p, con⟩ := o
    simp only [Option.map, rnOp]
    cases con <;> rfl

theorem condBrKind_holds_mapRegs (g : Reg → Reg) (k : CondBrKind) :
    (k.mapRegs g).holds = k.holds := by
  funext us w
  cases k <;> (cases us with
    | nil => rfl
    | cons a t => cases t <;> rfl)

theorem straightSem_mapRegs {F : BitVec 64 → Prop} {ctx : FnCtx} {g : Reg → Reg} {gn : Nat → Nat}
    (hg : VRenaming g gn) (i : MInst) : straightSem F ctx (i.mapRegs g) = straightSem F ctx i := by
  funext uses w
  unfold straightSem
  rw [operands_mapRegs hg]
  cases i.operands with
  | error e => rfl
  | ok ops =>
    simp only [Except.map]
    rw [canonRegs_rn, assign_mapRegs hg]
    have hz : ∀ (regs : Array Reg) (P : Operand → Bool), (∀ o, P (rnOp gn o) = P o) →
        ((((ops.map (rnOp gn)).zip regs).toList.filter (fun p => P p.1)).map Prod.snd) =
          (((ops.zip regs).toList.filter (fun p => P p.1)).map Prod.snd) := by
      intro regs P hP
      simp only [Array.toList_zip, Array.toList_map, zip_map_left]
      rw [filter_map_pair _ P hP, List.map_map]
      rfl
    have hp : ∀ (regs : Array Reg), placeUses (ops.map (rnOp gn)) regs uses w =
        placeUses ops regs uses w := fun regs => by
      unfold placeUses
      rw [hz regs Operand.isUse (fun _ => rfl)]
    have hd : ∀ (regs : Array Reg) t, defVals (ops.map (rnOp gn)) regs t = defVals ops regs t := by
      intro regs t
      unfold defVals
      rw [show ∀ (L : List (Operand × Reg)), L.map (fun p => regVal t p.2) =
        (L.map Prod.snd).map (regVal t) from fun L => by simp [List.map_map, Function.comp_def]]
      rw [hz regs Operand.isDef (fun _ => rfl)]
      simp [List.map_map, Function.comp_def]
    rw [hp (canonRegs ops)]
    simp only [hd]

theorem setTargets_cases {i : MInst} {ls : List Label} {i' : MInst}
    (h : i.setTargets ls = some i') :
    (∃ l l', i = .jump l ∧ i' = .jump l') ∨
    (∃ t e t' e' k, i = .condBr t e k ∧ i' = .condBr t' e' k) ∨
    (∃ kd t e t' e' rn bit, i = .testBitAndBranch kd t e rn bit ∧
      i' = .testBitAndBranch kd t' e' rn bit) ∨
    (∃ d ts d' ts' r t1 t2, i = .jtSequence d ts r t1 t2 ∧ i' = .jtSequence d' ts' r t1 t2 ∧
      ts'.length = ts.length) ∨
    (∃ info ti ti', i = .tryCall info ti ∧ i' = .tryCall info ti') := by
  unfold MInst.setTargets at h
  split at h
  all_goals (try split at h)
  all_goals first
    | (cases h; done)
    | (cases h; exact .inl ⟨_, _, rfl, rfl⟩)
    | (cases h; exact .inr (.inl ⟨_, _, _, _, _, rfl, rfl⟩))
    | (cases h; exact .inr (.inr (.inl ⟨_, _, _, _, _, _, _, rfl, rfl⟩)))
    | (rename_i hl
       cases h
       exact .inr (.inr (.inr (.inl ⟨_, _, _, _, _, _, _, rfl, rfl, by simpa using hl⟩))))
    | (cases h; exact .inr (.inr (.inr (.inr ⟨_, _, _, rfl, rfl⟩))))

/-- **`DriverSem` for `csem`.** -/
theorem driverSem_csem (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    DriverSem (csem F ctx X) where
  args := fun _ _ => rfl
  jump := fun _ _ => rfl
  rename := by
    intro g gn hg i
    funext uses w
    cases i with
    | call info =>
      obtain ⟨dest, us, ds⟩ := info
      cases dest <;> rfl
    | args ds => simp [csem, MInst.mapRegs, List.map_map, Function.comp_def]
    | rets us => rfl
    | jump l => rfl
    | condBr a b k => simp only [csem, MInst.mapRegs, condBrKind_holds_mapRegs]
    | testBitAndBranch k a b rn bit => rfl
    | trapIf k c => simp only [csem, MInst.mapRegs, condBrKind_holds_mapRegs]
    | udf c => rfl
    | jtSequence d ts ridx t1 t2 => rfl
    | loadExtNameGot rd n => rfl
    | loadExtNameNear rd n o => rfl
    | emitIsland n => rfl
    | _ =>
      rw [csem_straight rfl, csem_straight rfl, csemWF_mapRegs hg, mspec_mapRegs hg,
        straightSem_mapRegs hg]
  retarget := by
    intro i ls i' h
    funext uses w
    rcases setTargets_cases h with ⟨l, l', rfl, rfl⟩ | ⟨t, e, t', e', k, rfl, rfl⟩ |
      ⟨kd, t, e, t', e', rn, bit, rfl, rfl⟩ | ⟨d, ts, d', ts', r, t1, t2, rfl, rfl, hlen⟩ |
      ⟨info, ti, ti', rfl, rfl⟩
    · rfl
    · rfl
    · rfl
    · simp only [csem, hlen]
    · simp [csem, csemWF, FormOk, mspec, ispec]

/-! ## Calls -/

/-- **The contract of the external semantics** (the callees and the linker, outside the
function), for the externs `exts` a function declares: a call of the extern `ext ∈ exts` —
`bl name` (`some name`, uses = the arguments) or `blr` of its address (`none`, first use =
`X.sym name 0`) — with at most 8 arguments related to CLIF values `vals`, from a world related
(`MR`) to CLIF memory `cm`, where the CLIF extern returns `rvals` with memory `cm'`, returns one
value per ABI return of the declaration (`sigRets`: the declared returns, or for an `sret`
signature without returns the struct pointer, whose value is not constrained), the first ones
related to `rvals`, and a world related to `cm'`. For declarations without an `sret` parameter
this is the former contract (one value per result, related to the results). -/
def XCallsOk (env : Clif.Env) (exts : List Clif.ExtFunc) (MR : MemRelT) (X : ExtSem) : Prop :=
  ∀ ext ∈ exts, ∀ g (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem) (w : Arm.ArmState)
    (d : Option String) (uses args : List CV) (vals rvals : List Clif.Val) (cm' : Clif.Mem),
    env.extern ext.name = some g →
    (d = some ext.name ∧ uses = args ∨ d = none ∧ uses = ofX (X.sym ext.name 0) :: args) →
    vals.length ≤ 8 → AllHold vals args → MR sl cm w →
    g vals cm = .returned rvals cm' → rvals.length = ext.sig.returns.length →
    ∃ outs w', X.call d uses w = some (outs, w') ∧ outs.length = (sigRets ext.sig).length ∧
      PrefixHold rvals outs ∧ MR sl cm' w'

/-- `sigRets` of a signature without `sret` parameter is its declared returns. -/
theorem sigRets_of_noSret {s : Clif.Signature} (h : s.params.any (·.purpose == .sret) = false) :
    sigRets s = s.returns := by
  have hn : s.params.find? (·.purpose == .sret) = none := by
    rw [List.find?_eq_none]
    intro p hp hs
    have := List.any_eq_false.mp h p hp
    exact this hs
  unfold sigRets
  rw [hn]

/-- The former contract (every extern, one value per result, all related) implies `XCallsOk`
for declarations without `sret` parameter: for a function without `sret` callees the new
hypothesis is no stronger than the former one. -/
theorem xCallsOk_of_results {env : Clif.Env} {exts : List Clif.ExtFunc} {MR : MemRelT}
    {X : ExtSem} (hns : ∀ e ∈ exts, e.sig.params.any (·.purpose == .sret) = false)
    (h : ∀ (name : String) g (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem) (w : Arm.ArmState)
      (d : Option String) (uses args : List CV) (vals rvals : List Clif.Val) (cm' : Clif.Mem)
      (nd : Nat),
      env.extern name = some g →
      (d = some name ∧ uses = args ∨ d = none ∧ uses = ofX (X.sym name 0) :: args) →
      vals.length ≤ 8 → AllHold vals args → MR sl cm w →
      g vals cm = .returned rvals cm' → nd = rvals.length →
      ∃ outs w', X.call d uses w = some (outs, w') ∧ AllHold rvals outs ∧ MR sl cm' w') :
    XCallsOk env exts MR X := by
  intro ext hin g sl cm w d uses args vals rvals cm' hg hd hlen hall hmr hret hrl
  obtain ⟨outs, w', hc, ho, hm⟩ :=
    h ext.name g sl cm w d uses args vals rvals cm' rvals.length hg hd hlen hall hmr hret rfl
  exact ⟨outs, w', hc, by rw [sigRets_of_noSret (hns ext hin), ← hrl, ho.1], ho.prefixHold, hm⟩

/-- **`CallsRefine` for `csem`**, from the external contract. -/
theorem callsRefine_csem {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {env : Clif.Env}
    {exts : List Clif.ExtFunc} {MR : MemRelT} (hX : XCallsOk env exts MR X) :
    CallsRefine F env exts MR (csem F ctx X) := by
  refine ⟨fun n => X.sym n 0, fun rd n w => ⟨w, rfl, fun _ _ _ => rfl, fun _ _ => rfl, rfl⟩, ?_⟩
  intro ext hin g sl cm w dest us ds uses args vals rvals cm' hg hd hds hlen hall hmr hret hrl
  rcases hd with ⟨rfl, rfl⟩ | ⟨r, rfl, rfl⟩
  · obtain ⟨outs, w', hc, hol, ho, hm⟩ := hX ext hin g sl cm w (some ext.name) uses uses vals rvals
      cm' hg (.inl ⟨rfl, rfl⟩) hlen hall hmr hret hrl
    exact ⟨outs, w', by simp [csem, hc], by rw [hol, hds], ho, hm⟩
  · obtain ⟨outs, w', hc, hol, ho, hm⟩ := hX ext hin g sl cm w none _ args vals rvals cm'
      hg (.inr ⟨rfl, rfl⟩) hlen hall hmr hret hrl
    exact ⟨outs, w', by simp [csem, hc], by rw [hol, hds], ho, hm⟩

end Backend.Proof
