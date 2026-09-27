import FV.Backend.Proof.IselGeneric
import FV.Backend.Proof.IselData
import FV.Backend.Proof.RegallocOperands

/-!
# The isel contract: what M4 proves about the ISLE rules, and what M7 consumes

**Level.** Rule statements are about VCode: `MInst`s over virtual registers, run
straight-line (`seqRun`, `VStep`'s per-instruction rule) under an *abstract* per-instruction
semantics `isem : Sem` (values `CV`, world = the Arm state), exactly the semantics M6's
`checkAlloc_sound` simulates. M6's `csem F ctx` (the Arm model's execution of an instruction under
a canonical allocation) is the instance; the rules only need `Refines F isem`: `isem` agrees
with `ispec`, the value-level meaning of each emitted instruction form, up to the world
outside the allocatable registers (`SameWorld F`).

**Width convention** (PLAN.md §3.4): a CLIF value of type `ty` is the low `ty.width` bits of
its register (`VHolds`); upper bits are unspecified. Every rule obligation is local.

**Shapes.** `seqRun`, `LowerInstOk`, `LowerTermOk` and their pieces are the definitions agreed
with M7 (`Backend.Proof.Driver` in M7's placeholder, same definitions): the emitted code, run
from any vreg file holding the CLIF frame's values and any related world, computes the
instruction's results into fresh (or value) vregs, writes only fresh vregs, keeps the
memory relation `MR`, and stops at a halting instruction with the CLIF trap code for explicit
traps.

**Per rule.** `LowerRuleOk … r`: whenever root rule `r` of `lower` matches an instruction and
its right-hand side returns a value, the code it emitted satisfies `LowerInstOk`. Selection is
not needed ("the committed rule matched", `IselGeneric`): `lowerInstOk_of_rules` turns
`LowerRulesCorrect p` (every closure root rule is `LowerRuleOk`) plus `ExcludedUnmatchable p`
(the root rules outside the closure never match an E instruction) into `LowerInstOk` for every
successful `lower` call (`runTerm ctx "lower" …`, `lowerInstOk_runTerm`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-! ## Values and the width convention -/

/-- The VCode-level instruction semantics (M6's `csem F ctx` is the instance). -/
abbrev Sem := ISem CV Arm.ArmState

/-- A CLIF value of type `ty` is the low `ty.width` bits of a register value; the upper bits are
unspecified (PLAN.md §3.4). -/
def VHolds (v : Clif.Val) (x : CV) : Prop := x.setWidth v.ty.width = v.bits

/-- `vals` are held by `xs`, index by index. -/
def AllHold (vals : List Clif.Val) (xs : List CV) : Prop :=
  vals.length = xs.length ∧ ∀ (j : Nat) v x, vals[j]? = some v → xs[j]? = some x → VHolds v x

/-- Relation between the CLIF memory (with the activation's slot bases) and the VCode world. -/
abbrev MemRelT := List (Clif.SlotId × Nat) → Clif.Mem → Arm.ArmState → Prop

/-- Every defined CLIF value `x` is held by vreg `x` (`buildCtx`: value `x` has vreg `x`). -/
def ValsHeld (fr : Clif.Frame) (ρ : Nat → CV) : Prop :=
  ∀ x v, fr.regs x = some v → VHolds v (ρ x)

/-! ## Straight-line VCode execution (`VStep`'s per-instruction rule) -/

section
variable {V W : Type}

/-- Use values of an instruction with operands `ops` in the vreg file `ρ`. -/
def vuses (ops : Array Operand) (ρ : Nat → V) : List V :=
  (ops.toList.filter Operand.isUse).map (ρ ·.vreg)

/-- `VStep`'s register-file update: early defs, then late defs. -/
def vdefUpd (ops : Array Operand) (outs : List V) (ρ : Nat → V) : Nat → V :=
  writeV (writeV ρ (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isEarly)))
    (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isLate))

/-- Def vregs of an instruction (empty if it has no operand view). -/
def vdefs (i : MInst) : List Nat :=
  match i.operands with
  | .ok ops => (ops.toList.filter Operand.isDef).map (·.vreg)
  | .error _ => []

/-- Use vregs of an instruction (empty if it has no operand view). -/
def vuseNums (i : MInst) : List Nat :=
  match i.operands with
  | .ok ops => (ops.toList.filter Operand.isUse).map (·.vreg)
  | .error _ => []

/-- How a straight-line run ended. `stop k i ops ρ w outs w' ctl`: instruction `k` (`i`,
operands `ops`) ran in state `ρ, w`, produced `outs, w'` and control `ctl ≠ next`. -/
inductive SeqEnd (V W : Type) where
  | fall (ρ : Nat → V) (w : W)
  | stop (k : Nat) (i : MInst) (ops : Array Operand) (ρ : Nat → V) (w : W) (outs : List V)
      (w' : W) (ctl : Ctl)

def SeqEnd.succ : SeqEnd V W → SeqEnd V W
  | .fall ρ w => .fall ρ w
  | .stop k i ops ρ w outs w' ctl => .stop (k + 1) i ops ρ w outs w' ctl

/-- Straight-line run of `ms`. -/
def seqRun (sem : ISem V W) : List MInst → (Nat → V) → W → Option (SeqEnd V W)
  | [], ρ, w => some (.fall ρ w)
  | i :: ms, ρ, w =>
    match i.operands with
    | .error _ => none
    | .ok ops =>
      match sem i (vuses ops ρ) w with
      | none => none
      | some (outs, w', ctl) =>
        if outs.length = (ops.toList.filter Operand.isDef).length then
          match ctl with
          | .next => (seqRun sem ms (vdefUpd ops outs ρ) w').map SeqEnd.succ
          | ctl => some (.stop 0 i ops ρ w outs w' ctl)
        else none

end

/-! ## The value-level spec of the emitted instruction forms -/

/-- The operand at an operation size: the low `sz.bits` bits of the register. -/
def opnd (sz : OperandSize) (a : CV) : BitVec sz.bits := (lo64 a).setWidth sz.bits

/-- A result at an operation size, zero-extended into the 64-bit register. -/
def resX (sz : OperandSize) (r : BitVec sz.bits) : CV := ofX (r.setWidth 64)

/-- The def outputs of an instruction with destination `rd` (a real register such as `xzr` is
not an operand, so it has no output). -/
def defOut (rd : Reg) (x : CV) : List CV :=
  match rd with
  | .vreg .. => [x]
  | _ => []

/-- The non-flag-setting two-operand ALU operations, at width `n`. -/
def aluVal {n : Nat} (op : ALUOp) (a b : BitVec n) : Option (BitVec n) :=
  match op with
  | .add => some (a + b)
  | .sub => some (a - b)
  | .and => some (a &&& b)
  | .orr => some (a ||| b)
  | .eor => some (a ^^^ b)
  | _ => none

/-- **Value-level meaning of the instruction forms the proven rules emit**, in terms of the
Arm model's operations (`AddWithCarry`, `write_pstate`, `ConditionHolds`): the def values
(in operand order) and the world after. `none`: form not specified (yet). A 32-bit operation
reads the low 32 bits of its operands and zero-extends its result (Arm `W` registers). -/
def ispec : Sem := fun i uses w =>
  match i, uses with
  | .aluRRR .subS sz rd _ _, [a, b] =>
    let r := Arm.AddWithCarry (opnd sz a) (~~~(opnd sz b)) 1#1
    some (defOut rd (resX sz r.1), Arm.write_pstate r.2 w, .next)
  | .aluRRR .lsr .size32 rd _ _, [a, b] =>
    some (defOut rd (resX .size32 (opnd .size32 a >>> ((opnd .size32 b).toNat % 32))), w, .next)
  | .aluRRR op sz rd _ _, [a, b] =>
    (aluVal op (opnd sz a) (opnd sz b)).map fun r => (defOut rd (resX sz r), w, .next)
  | .aluRRImm12 .add sz rd _ imm, [a] =>
    if imm.bits < 4096 then
      some (defOut rd (resX sz (opnd sz a + BitVec.ofNat _ imm.value)), w, .next)
    else none
  | .aluRRImmLogic op sz rd _ imm, [a] =>
    if ImmLogic.ofNat? imm.value sz = some imm then
      (aluVal op (opnd sz a) (BitVec.ofNat _ imm.value)).map fun r =>
        (defOut rd (resX sz r), w, .next)
    else none
  | .extend rd _ sg fromB toB, [a] =>
    if (fromB = 8 ∨ fromB = 16 ∨ fromB = 32) ∧ (toB = 32 ∨ toB = 64) ∧ fromB < toB then
      let x := (lo64 a).setWidth fromB
      let r : BitVec 64 :=
        if sg then (x.signExtend toB).setWidth 64 else (x.setWidth toB).setWidth 64
      some (defOut rd (ofX r), w, .next)
    else none
  | .cset rd c, [] =>
    if c = .al ∨ c = .nv then none
    else some (defOut rd (ofX (if Arm.ConditionHolds c.invert.bits w then 0#64 else 1#64)), w, .next)
  | _, _ => none

/-- **The semantic hypothesis of the rule statements**: on every form `ispec` specifies, the
VCode semantics gives the same def values and the same control (`ispec` only produces `next`,
and `halt` for the trap forms), with a world that agrees with `ispec`'s outside the
allocatable registers and the frame addresses `F` (M6's `SameWorld`). M6's `csem F ctx`
satisfies it form by form (its characterization lemmas). -/
def Refines (F : BitVec 64 → Prop) (isem : Sem) : Prop :=
  ∀ i us w outs w' {ctl : Ctl}, ispec i us w = some (outs, w', ctl) →
    ∃ w'', isem i us w = some (outs, w'', ctl) ∧ SameWorld F w'' w'

/-- `SameWorld` without NZCV: `s` and `t` agree on every unmasked field except the flags, on
memory outside `F`, and on the program. -/
def SameWorldNF (F : BitVec 64 → Prop) (s t : Arm.ArmState) : Prop :=
  (∀ f, ¬ Masked f → (∀ fl, f ≠ .FLAG fl) → Arm.r f s = Arm.r f t) ∧
    (∀ a, ¬ F a → s.mem a = t.mem a) ∧ s.program = t.program

/-- The memory relation does not depend on the allocatable registers, the pc or the flags
(which is all the non-memory instructions change). -/
def MRStable (F : BitVec 64 → Prop) (MR : MemRelT) : Prop :=
  ∀ sl cm w w', SameWorldNF F w' w → MR sl cm w → MR sl cm w'

/-! ## The lowering context -/

/-- Facts about the lowering context `buildCtx f` builds (M7 proves `buildCtx f = .ok (ctx, …)
→ CtxInv f ctx`): instruction data is `instData` of the CLIF instruction, result types are the
CLIF result types, value `x` has vreg `x`, value definitions point at instructions, stack slot
offsets are `slotLayout`'s. -/
structure CtxInv (f : Clif.Function) (ctx : Ctx) : Prop where
  func : ctx.func = f
  data : ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info → info.clif = some inst →
    instData f inst = .ok info.data
  resTys : ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info → info.clif = some inst →
    ∃ tys, inst.resultTypes (fun r => (f.extern? r).map (·.sig)) = some tys ∧
      info.resTys = tys.map CTy.ofClif ∧ info.results.length = tys.length
  valueReg : ∀ (x : Nat) (r : Reg), ctx.valueReg? x = some r → r = .vreg x .int
  typedReg : ∀ (x : Nat) (t : CTy), ctx.valueType? x = some t → ctx.valueReg? x = some (.vreg x .int)
  defInst : ∀ (x d : Nat), ctx.defInst? x = some d → ∃ info, ctx.insts[d]? = some info ∧ x ∈ info.results
  slotOff : ctx.slotOff = (slotLayout f.slots).1

/-- Instructions the rules may look through (`def_inst`): their value is a function of their
operands (and the frame's slot bases). -/
def pureInst : Clif.Inst → Bool
  | .iconst .. | .unary .. | .binary .. | .icmp .. | .extend .. | .ireduce .. | .select ..
  | .stackAddr .. => true
  | _ => false

/-- The frame is typed as the context says: a defined value's CLIF type is its `valueType?`
(`buildCtx` sets `valTy` from the declared parameter/result types). Rules dispatching on
`value_type` (`extended_value_from_value`, `put_in_reg_zext32/sext32/zext64/sext64`, …) need
it. -/
def FrameTyped (ctx : Ctx) (fr : Clif.Frame) : Prop :=
  ∀ (x : Nat) (t : CTy) (v : Clif.Val), ctx.valueType? x = some t → fr.regs x = some v →
    CTy.ofClif v.ty = t

/-- DFG consistency: a defined value whose definition is a pure instruction equals that
instruction re-evaluated in the current frame (what `def_inst` look-through relies on), and
the frame is typed as the context says (`FrameTyped`). -/
def DFGCons (ctx : Ctx) (fr : Clif.Frame) : Prop :=
  (∀ (x j : Nat) (info : IInfo) (cl : Clif.Inst) (v : Clif.Val), ctx.defInst? x = some j → ctx.insts[j]? = some info → info.clif = some cl →
    pureInst cl = true → fr.regs x = some v →
    ∃ vals, (∀ cm, Clif.evalInst fr cm cl = .ok (vals, cm)) ∧ (info.results.zip vals).lookup x = some v) ∧
  FrameTyped ctx fr

/-! ## The per-instruction obligation (agreed with M7) -/

/-- The CLIF outcome of a statement's instruction: `evalInst`, and for a `call` the extern's
semantics (as `Clif.stepCall`; a call of a function of `p` is outside the theorem). -/
def instOutcome (env : Clif.Env) (p : Clif.Program) (fr : Clif.Frame) (cm : Clif.Mem) :
    Clif.Inst → Clif.Res (List Clif.Val × Clif.Mem)
  | .call fn args =>
    Clif.Res.bind (do
      let ext ← Clif.Res.ofOption s!"unknown function reference fn{fn}" (fr.func.extern? fn)
      let vals ← fr.getMany args
      Clif.checkTys s!"arguments of call to %{ext.name}" vals (Clif.AbiParam.tys ext.sig.params)
      pure (ext, vals)) fun (ext, vals) =>
    match p.func? ext.name with
    | some _ => .stuck "call of a function of the program"
    | none =>
      match env.extern ext.name with
      | some g =>
        match g vals cm with
        | .returned rvals mem' =>
          if rvals.map (·.ty) == Clif.AbiParam.tys ext.sig.returns then .ok (rvals, mem')
          else .stuck s!"extern %{ext.name} returned values of the wrong types"
        | .trapped c => .trap c
        | .stuck m => .stuck m
        | .outOfFuel => .stuck s!"extern %{ext.name} ran out of fuel"
      | none => .stuck s!"unknown callee %{ext.name}"
  | i => Clif.evalInst fr cm i

/-- Instructions whose trap the lowering makes explicit (check + trap instruction). -/
def explicitTrapInst : Clif.Inst → Bool
  | .div .. => true
  | _ => false

/-- Trap code of a trapping VCode instruction. -/
def trapCode? : MInst → Option Clif.TrapCode
  | .udf c | .trapIf _ c => some c
  | _ => none

/-- The result registers hold the results: one virtual register per result, a fresh vreg
(`≥ lo`) or a defined value's vreg. -/
def ResultsHeld (lo : Nat) (fr : Clif.Frame) (rss : List (List Reg)) (vals : List Clif.Val)
    (ρ : Nat → CV) : Prop :=
  rss.length = vals.length ∧
    ∀ (j : Nat) rs v, rss[j]? = some rs → vals[j]? = some v →
      ∃ out cls, rs = [.vreg out cls] ∧ (lo ≤ out ∨ (fr.regs out).isSome) ∧ VHolds v (ρ out)

/-- The emitted code reads only fresh vregs (`≥ st.nextVreg`) or vregs of values defined in
`fr`. Required on the runs that continue (an undefined operand makes CLIF `stuck`). -/
def UsesOk (st : LState) (fr : Clif.Frame) (ms : List MInst) : Prop :=
  ∀ m ∈ ms, ∀ u ∈ vuseNums m, st.nextVreg ≤ u ∨ (fr.regs u).isSome

/-- **`lower` on a non-terminator** (results `results`; lowering state `st` → `st'`, emitted
code `ms`). -/
structure LowerInstOk (isem : Sem) (MR : MemRelT) (env : Clif.Env) (p : Clif.Program)
    (ctx : Ctx) (inst : Clif.Inst) (results : List Nat) (st : LState) (rss : List (List Reg))
    (st' : LState) (ms : List MInst) : Prop where
  mono : st.nextVreg ≤ st'.nextVreg
  defs : ∀ m ∈ ms, ∀ d ∈ vdefs m, st.nextVreg ≤ d ∧ d < st'.nextVreg
  run : ∀ (fr : Clif.Frame) (cm : Clif.Mem) (ρ : Nat → CV) (w : Arm.ArmState),
    fr.func = ctx.func → ValsHeld fr ρ → DFGCons ctx fr → MR fr.slots cm w →
    match instOutcome env p fr cm inst with
    | .ok (vals, cm') => UsesOk st fr ms ∧ ∃ ρ' w', seqRun isem ms ρ w = some (.fall ρ' w') ∧
        (results = [] ∨ ResultsHeld st.nextVreg fr rss vals ρ') ∧ MR fr.slots cm' w'
    | .trap c => explicitTrapInst inst = true → UsesOk st fr ms ∧
        ∃ k i ops ρ₁ w₁ outs w₂, seqRun isem ms ρ w = some (.stop k i ops ρ₁ w₁ outs w₂ .halt) ∧
          trapCode? i = some c
    | .stuck _ => True

/-- The successor a branch takes, as an index into the driver's target list (`jump`: its
target; `brif`: then, else; `br_table`: default, then the table). -/
def branchIdx (fr : Clif.Frame) : Clif.Terminator → Clif.Res Nat
  | .jump _ => .ok 0
  | .brif c _ _ => Clif.Res.bind (fr.get c) fun v => .ok (if Clif.Sem.truthy v.bits then 0 else 1)
  | .brTable x _ tbl => Clif.Res.bind (fr.get x) fun v =>
      .ok (if v.toNat < tbl.length then v.toNat + 1 else 0)
  | _ => .stuck "not a branch"

/-- **`lower` on `return`/`trap`, `lower_branch` on a branch** (terminator `t`). -/
structure LowerTermOk (isem : Sem) (MR : MemRelT) (ctx : Ctx) (t : Clif.Terminator)
    (targets : List Label) (st st' : LState) (ms : List MInst) : Prop where
  mono : st.nextVreg ≤ st'.nextVreg
  defs : ∀ m ∈ ms, ∀ d ∈ vdefs m, st.nextVreg ≤ d ∧ d < st'.nextVreg
  run : ∀ (fr : Clif.Frame) (cm : Clif.Mem) (ρ : Nat → CV) (w : Arm.ArmState),
    fr.func = ctx.func → ValsHeld fr ρ → DFGCons ctx fr → MR fr.slots cm w →
    match t with
    | .ret xs => ∀ vals, fr.getMany xs = .ok vals → UsesOk st fr ms ∧
        ∃ k us ops ρ₁ w₁ outs w₂,
          seqRun isem ms ρ w = some (.stop k (.rets us) ops ρ₁ w₁ outs w₂ .ret) ∧
          us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = vals.length ∧
          AllHold vals (vuses ops ρ₁) ∧ MR fr.slots cm w₂
    | .trap c => UsesOk st fr ms ∧ ∃ k i ops ρ₁ w₁ outs w₂,
        seqRun isem ms ρ w = some (.stop k i ops ρ₁ w₁ outs w₂ .halt) ∧ trapCode? i = some c
    | t => (∀ i, ms.getLast? = some i → i.targets = targets) ∧ ∀ j, branchIdx fr t = .ok j →
        UsesOk st fr ms ∧ ∃ k i ops ρ₁ w₁ outs w₂,
          seqRun isem ms ρ w = some (.stop k i ops ρ₁ w₁ outs w₂ (.goto j)) ∧ k + 1 = ms.length ∧
          MR fr.slots cm w₂

/-! ## Per-rule statements and the M4 target predicate -/

/-- Rule `r` is a root rule of the emitter-subset closure (`Isle.Aarch64.Closure`). -/
def closureRoot (r : Rule) : Bool := Closure.rules.any fun c => c.isRoot && c.rule == r.id

/-- The vreg of every value with a register is below the lowering state's next fresh vreg
(`buildCtx` starts `nextVreg` above every value's vreg and lowering only increases it), so
fresh temporaries never alias an operand. -/
def ValsBelow (ctx : Ctx) (st : LState) : Prop :=
  ∀ (x : Nat) (r : Reg), ctx.valueReg? x = some r → x < st.nextVreg

/-- **Root rule correctness (`lower`).** Whenever rule `r` matches instruction `ii` (from any
lowering state) and its right-hand side returns `out`, the instructions it appended are a
correct lowering of the CLIF instruction: `out` lists the result registers and
`LowerInstOk` holds. Stated for all fuels `≥ 1000` (the driver runs with fuel 10⁶; a rule
needs a bounded amount, so the lemmas never need fuel monotonicity). -/
def LowerRuleOk (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInv f ctx → ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info → info.clif = some inst →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n → ValsBelow ctx st →
    (matchRule p (sem ctx) cfg m r [.inst ii]).run (st, tr) = .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx inst info.results st rss st' ms

/-- **M4's target (`lower`).** For every VCode semantics refining `ispec` and every stable
memory relation, every root rule of `lower` in the E-closure is correct. This is the M4
hypothesis of M7's theorem (with `data_program`: `lowerInstOk_runTerm`). -/
def LowerRulesCorrect (p : Program) : Prop :=
  ∀ (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program),
    Refines F isem → MRStable F MR →
    ∀ r ∈ p.rulesOf TId.lower, closureRoot r = true → LowerRuleOk isem MR env cp p r

/-- The root rules of `lower` outside the closure (their patterns name a non-E opcode, a
non-`i8..i64` type or a vector/float type test) never match an instruction of a context
`buildCtx` builds. -/
def ExcludedUnmatchable (p : Program) : Prop :=
  ∀ r ∈ p.rulesOf TId.lower, closureRoot r = false →
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInv f ctx → ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info → info.clif = some inst →
  ∀ (cfg : Config) (m : Nat) (s : LState × Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId),
    (matchRule p (sem ctx) cfg m r [.inst ii]).run s ≠ .ok (some env', s1)

/-- **Root rule correctness (`lower_branch`)**, on the terminator `t` lowered in the driver's
context `ctx` (instruction `ti` holds the terminator's data), with branch targets `targets`. -/
def BranchRuleOk (isem : Sem) (MR : MemRelT) (p : Program) (r : Rule) : Prop :=
  ∀ (ctx : Ctx) (ti : Nat) (t : Clif.Terminator) (data : V) (targets : List Label), termData t = .ok data →
  ctx.insts[ti]? = some ⟨data, [], [], none⟩ →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n →
    (matchRule p (sem ctx) cfg m r [.inst ti, .labels targets]).run (st, tr) =
      .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧ LowerTermOk isem MR ctx t targets st st' ms

/-- M4's target for `lower_branch` (not proven yet; stated for M7). -/
def BranchRulesCorrect (p : Program) : Prop :=
  ∀ (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT),
    Refines F isem → MRStable F MR →
    ∀ r ∈ p.rulesOf TId.lower_branch, closureRoot r = true → BranchRuleOk isem MR p r

/-! ## From the rules to every `lower` call -/

theorem lowerInstOk_of_rules {p : Program} (hp : Data p) (hrules : LowerRulesCorrect p)
    (hex : ExcludedUnmatchable p) {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem) (hMR : MRStable F MR)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {cfg : Config} (hco : cfg.checkOverlap = false) {n : Nat}
    (hn : 1002 + (p.rulesOf TId.lower).length ≤ n) {ty : TypeId} {st : LState}
    {tr : Array RuleId} {out : V} {st' : LState} {tr' : Array RuleId} (hvb : ValsBelow ctx st)
    (h : (applyTerm p (sem ctx) cfg (n + 1) ty TId.lower [.inst ii]).run (st, tr) =
      .ok (some out, (st', tr'))) :
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx inst info.results st rss st' ms := by
  change 1002 + (p.rulesOf 686).length ≤ n at hn
  obtain ⟨r, hr, m, env', s1, st2, tr2, hmn, hmatch, heval, hs⟩ :=
    applyTerm_internal_some hco hp.t686 term_686_kind rfl h
  simp only [Prod.mk.injEq] at hs
  rw [← hs.1] at heval
  cases hroot : closureRoot r
  · exact absurd hmatch (hex r hr hroot f ctx hctx ii info inst hi hc cfg m (st, tr) env' s1)
  · exact hrules F isem MR env cp hR hMR r hr hroot f ctx hctx ii info inst hi hc cfg hco m n st tr
      env' s1 out st' tr2 (by omega) (by omega) hvb hmatch heval

set_option maxRecDepth 20000 in
/-- `lowerInstOk_of_rules` for the exported program and the backend's own call
(`runTerm ctx "lower" [.inst ii]`, as `lowerFunction` makes it). -/
theorem lowerInstOk_runTerm (hrules : LowerRulesCorrect program)
    (hex : ExcludedUnmatchable program) {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem) (hMR : MRStable F MR)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {st : LState} {out : V} {st' : LState} {tr : List RuleId} (hvb : ValsBelow ctx st)
    (h : runTerm ctx "lower" [.inst ii] st = .ok (some out, st', tr)) :
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx inst info.results st rss st' ms := by
  unfold runTerm Interp.run at h
  rw [program_termByName_lower] at h
  dsimp only at h
  cases ha : (applyTerm program (sem ctx) {} 1000000 T.lower.ret T.lower.id [.inst ii]).run
      (st, #[]) with
  | error e => rw [ha] at h; cases h
  | ok q =>
    obtain ⟨v, st2, tr2⟩ := q
    rw [ha] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    injection h with h
    injection h with h1 h2
    subst h1
    injection h2 with h2 _
    subst h2
    have hlen : (program.rulesOf TId.lower).length ≤ 1000 := by
      rw [show TId.lower = 686 from rfl, data_program.r686]; decide
    obtain ⟨ms, rss, h1, h2, h3⟩ := lowerInstOk_of_rules data_program hrules hex hR hMR hctx hi hc
      rfl (by omega) hvb ha
    exact ⟨ms, rss, by simpa using h1, h2, h3⟩

end Backend.Proof
