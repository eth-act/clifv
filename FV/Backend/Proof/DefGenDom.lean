import FV.Backend.Proof.KillBase
import FV.Backend.Proof.IselFlowCheck

/-!
# Definedness of the ISLE runs (`DefRunsHyp`): the abstract interpreter

A flow-sensitive, symbolic abstract interpretation of ISLE rules. Abstract values `A` describe
values relative to a set of *defined* vregs `D` and the rule's variable environment
(`DefGenSem`):

* `cl b z`: clean: every register is defined (a vreg in `D`; a real register only if `z`, and
  then not allocatable), every CLIF value is reached, every instruction is reached (the root
  instruction only if `b`);
* `wr z`: a pending register value (a temporary before the instruction defining it is emitted):
  its vregs are fresh or defined;
* `ty τ`: the type predicate of `MInst` (uses defined), of the flag/side-effect types (their
  instructions, emitted in field order, read defined vregs or defs of earlier ones; their result
  registers are defined once all are emitted), of `CondResult` and of the call infos;
* `sym x`: the value of variable `x` (identity, so that emitting an instruction holding `x` in a
  def field makes `x` defined);
* `aft ys a`: `a` holds once the instructions held by variables `ys` are emitted;
* `data τ k fs`, `regs as`: structure; `crl xs`, `cinfo xs`: a call's return list / info whose
  defs hold the registers of the variables `xs`.

Abstract environments `AEnv` map each variable to `none` (unbound) or its abstract value;
variables are bound once. Every internal term gets a summary from its signature (`argA`,
`retA`), every rule of the closure `defTab` is checked (`aRule`), and the extern constructors
(`actor`), extractors (`aext`), the two emitting oracle terms (`emit_side_effect`, `side_effect`)
and the constructor-tree terms (`wrapper`) have transfer functions.
-/

namespace Backend.Proof.DefGen

open Backend Isle Isle.Aarch64 Isle.Interp

/-- Abstract values. -/
inductive A where
  | top
  | cl (b z : Bool)
  | wr (z : Bool)
  | ty (t : TypeId) (z : Bool)
  | sym (x : Nat)
  | aft (ys : List Nat) (a : A)
  | data (t : TypeId) (k : Nat) (fs : List A)
  | regs (as : List A)
  | crl (xs : List Nat)
  | cinfo (xs : List Nat)
  deriving Repr, Inhabited

/-- Abstract environments: per variable, unbound (`none`) or its abstract value. -/
abbrev AEnv := List (Option A)

/-! ## Tables -/

/-- Kinds of the fields of a modelled `MInst` variant: def register, use (registers read),
call info. -/
inductive FK where
  | d | u | c
  deriving DecidableEq, Repr

/-- The field kinds of the `MInst` variants `MInst.ofV` models (`none`: not modelled). -/
def miKinds (k : Nat) : Option (List FK) :=
  match k with
  | VIdx.MInst.AluRRR => some [.u, .u, .d, .u, .u]
  | VIdx.MInst.AluRRRR => some [.u, .u, .d, .u, .u, .u]
  | VIdx.MInst.AluRRImm12 => some [.u, .u, .d, .u, .u]
  | VIdx.MInst.AluRRImmLogic => some [.u, .u, .d, .u, .u]
  | VIdx.MInst.AluRRImmShift => some [.u, .u, .d, .u, .u]
  | VIdx.MInst.AluRRRShift => some [.u, .u, .d, .u, .u, .u]
  | VIdx.MInst.AluRRRExtend => some [.u, .u, .d, .u, .u, .u]
  | VIdx.MInst.BitRR => some [.u, .u, .d, .u]
  | VIdx.MInst.Mov => some [.u, .d, .u]
  | VIdx.MInst.MovWide => some [.u, .d, .u, .u]
  | VIdx.MInst.MovK => some [.d, .u, .u, .u]
  | VIdx.MInst.Extend => some [.d, .u, .u, .u, .u]
  | VIdx.MInst.BitfieldMove => some [.u, .u, .d, .u, .u, .u]
  | VIdx.MInst.CSet => some [.d, .u]
  | VIdx.MInst.CSel => some [.d, .u, .u, .u]
  | VIdx.MInst.CCmp => some [.u, .u, .u, .u, .u]
  | VIdx.MInst.CCmpImm => some [.u, .u, .u, .u, .u]
  | VIdx.MInst.MovToFpu => some [.d, .u, .u]
  | VIdx.MInst.MovFromVec => some [.d, .u, .u, .u]
  | VIdx.MInst.VecMisc => some [.u, .d, .u, .u]
  | VIdx.MInst.VecLanes => some [.u, .d, .u, .u]
  | VIdx.MInst.VecRRR => some [.u, .d, .u, .u, .u]
  | VIdx.MInst.Call => some [.c]
  | VIdx.MInst.CallInd => some [.c]
  | VIdx.MInst.Jump => some [.u]
  | VIdx.MInst.CondBr => some [.u, .u, .u]
  | VIdx.MInst.TestBitAndBranch => some [.u, .u, .u, .u, .u]
  | VIdx.MInst.TrapIf => some [.u, .u]
  | VIdx.MInst.Udf => some [.u]
  | VIdx.MInst.JTSequence => some [.u, .u, .u, .d, .d]
  | VIdx.MInst.LoadExtNameGot => some [.d, .u]
  | VIdx.MInst.LoadExtNameNear => some [.d, .u, .u]
  | VIdx.MInst.LoadAddr => some [.d, .u]
  | VIdx.MInst.EmitIsland => some [.u]
  | VIdx.MInst.LoadAcquire => some [.u, .d, .u, .u]
  | VIdx.MInst.StoreRelease => some [.u, .u, .u, .u]
  | VIdx.MInst.AtomicRMWLoop => some [.u, .u, .u, .u, .u, .d, .d, .d]
  | VIdx.MInst.AtomicCASLoop => some [.u, .u, .u, .u, .u, .d, .d]
  | VIdx.MInst.CSetm => some [.d, .u]
  | VIdx.MInst.Fence => some []
  | VIdx.MInst.ElfTlsGetAddr => some [.u, .d, .d]
  | k =>
    match loadOpOfIdx? k, storeOpOfIdx? k with
    | some _, _ => some [.d, .u, .u]
    | none, some _ => some [.u, .u, .u]
    | none, none => none

/-- Kinds of the fields of a flag/side-effect variant: an instruction (emitted in field order),
a result register (defined once every instruction is emitted), other. -/
inductive SK where
  | i | r | o
  deriving DecidableEq, Repr

/-- The flag/side-effect types. -/
def flagTys : List TypeId :=
  [TyId.«SideEffectNoResult», TyId.«ProducesFlags», TyId.«ConsumesAndProducesFlags»,
   TyId.«ConsumesFlags»]

/-- The shapes of the flag/side-effect variants. -/
def flagShape (τ k : Nat) : Option (List SK) :=
  match τ, k with
  | TyId.«SideEffectNoResult», 0 => some [.i]
  | TyId.«SideEffectNoResult», 1 => some [.i, .i]
  | TyId.«SideEffectNoResult», 2 => some [.i, .i, .i]
  | TyId.«ProducesFlags», 0 => some []
  | TyId.«ProducesFlags», 1 => some [.i]
  | TyId.«ProducesFlags», 2 => some [.i, .i]
  | TyId.«ProducesFlags», 3 => some [.i, .r]
  | TyId.«ProducesFlags», 4 => some [.i, .r]
  | TyId.«ProducesFlags», 5 => some [.i, .r, .o]
  | TyId.«ProducesFlags», 6 => some [.i, .r, .o, .i]
  | TyId.«ConsumesAndProducesFlags», 0 => some [.i]
  | TyId.«ConsumesAndProducesFlags», 1 => some [.i, .r]
  | TyId.«ConsumesFlags», 0 => some [.i]
  | TyId.«ConsumesFlags», 1 => some [.i, .i]
  | TyId.«ConsumesFlags», 2 => some [.i, .r]
  | TyId.«ConsumesFlags», 3 => some [.i, .r]
  | TyId.«ConsumesFlags», 4 => some [.i, .i, .r]
  | TyId.«ConsumesFlags», 5 => some [.i, .i, .i, .i, .r]
  | TyId.«ConsumesFlags», 6 => some []
  | _, _ => none

/-- The shapes of the `CondResult` variants (`true`: a `ProducesFlags` field). -/
def crShape (τ k : Nat) : Option (List Bool) :=
  match τ, k with
  | TyId.«CondResult», 0 => some [false, false]
  | TyId.«CondResult», 1 => some [false, false]
  | TyId.«CondResult», 2 => some [true, false]
  | TyId.«CondResult», 3 => some [true, false, false]
  | TyId.«CondResult», 4 => some [true, false, false]
  | _, _ => none

/-- The call info types. -/
def ciTys : List TypeId := [TyId.«BoxCallInfo», TyId.«BoxCallIndInfo»]

/-- The types with a relational predicate (`ty τ`). -/
def relTy (τ : TypeId) : Bool :=
  τ == tyMInst || flagTys.contains τ || τ == TyId.«CondResult» || ciTys.contains τ

/-- The summary of a value of type `τ` (`z`: real registers allowed). -/
def tyA (z : Bool) (τ : TypeId) : A :=
  if τ == TyId.«WritableReg» || τ == TyId.«WritableValueRegs» then .wr z
  else if τ == TyId.«Inst» then .cl true false
  else if relTy τ then .ty τ z
  else .cl false z

/-! ## Resolution and the order -/

/-- The fuel of resolution (longer than any alias chain of a rule). -/
def F : Nat := 64

/-- Look through variables and empty `aft`. -/
def res (e : AEnv) : Nat → A → A
  | 0, _ => .top
  | n + 1, .sym x => match e.getD x none with
    | some a => res e n a
    | none => .top
  | n + 1, .aft [] a => res e n a
  | _, a => a

/-- `a` is clean (root allowed iff `b`, real registers iff `z`). -/
def fitsCl (e : AEnv) : Nat → Bool → Bool → A → Bool
  | 0, _, _, _ => false
  | n + 1, b, z, a => match res e n a with
    | .cl b' z' => (!b' || b) && (!z' || z)
    | .data _ _ fs => fitsClL e n b z fs
    | .regs as => fitsClL e n b z as
    | _ => false
where
  /-- `fitsCl` of a list. -/
  fitsClL (e : AEnv) (n : Nat) (b z : Bool) : List A → Bool
    | [] => true
    | a :: as => fitsCl e n b z a && fitsClL e n b z as

/-- `a` is a pending or defined register value. -/
def fitsWr (e : AEnv) (n : Nat) (z : Bool) (a : A) : Bool :=
  match res e n a with
  | .wr z' => !z' || z
  | .cl _ z' => !z' || z
  | _ => false

/-- `a` is a call info whose uses are defined. -/
def fitsCI (e : AEnv) (n : Nat) (a : A) : Bool :=
  match res e n a with
  | .ty τ _ => ciTys.contains τ
  | .cinfo _ => true
  | .cl _ _ => true
  | _ => false

/-- The fields of a modelled `MInst` variant fit their kinds. -/
def fitsFields (e : AEnv) (n : Nat) : List A → List FK → Bool
  | f :: fs, k :: ks =>
    (match k with
     | .d => fitsWr e n true f
     | .u => fitsCl e n true true f
     | .c => fitsCI e n f) && fitsFields e n fs ks
  | [], [] => true
  | _, _ => false

/-- `a` is an `MInst` value whose uses are defined. -/
def fitsMI (e : AEnv) (n : Nat) (a : A) : Bool :=
  match res e n a with
  | .ty τ _ => τ == tyMInst
  | .cl _ _ => true
  | .data τ k fs => τ == tyMInst && (match miKinds k with
    | some ks => fitsFields e n fs ks
    | none => true)
  | _ => false

/-! ## Upgrades: emitting an instruction -/

/-- `ys` without `y`, as an `aft`. -/
def dropAft1 (y : Nat) : Option A → Option A
  | some (.aft ys b) => some (if (ys.erase y).isEmpty then b else .aft (ys.erase y) b)
  | o => o

/-- Emitting the instruction of variable `y`: `aft` lists lose `y`. -/
def dropAft (y : Nat) (e : AEnv) : AEnv := e.map (dropAft1 y)

/-- Variable `x` (a pending register) is now defined. -/
def setDef (e : AEnv) (n : Nat) (x : Nat) : AEnv :=
  match res e n (.sym x) with
  | .wr z => e.set x (some (.cl false z))
  | _ => e

/-- `setDef` of each variable. -/
def setDefL (e : AEnv) (n : Nat) : List Nat → AEnv
  | [] => e
  | x :: xs => setDefL (setDef e n x) n xs

/-- The upgrade of one field of an emitted instruction. -/
def upg1 (e : AEnv) (n : Nat) (f : A) : FK → AEnv
  | .d => match f with
    | .sym x => setDef e n x
    | _ => e
  | .c => match res e n f with
    | .cinfo xs => setDefL e n xs
    | _ => e
  | .u => e

/-- The upgrades of the fields of an emitted instruction. -/
def upgF (e : AEnv) (n : Nat) : List A → List FK → AEnv
  | f :: fs, k :: ks => upgF (upg1 e n f k) n fs ks
  | _, _ => e

/-- All bound variables become clean (after a call that never returns). -/
def deadEnv (e : AEnv) : AEnv := e.map fun o => o.map fun _ => .cl false false

/-- The upgrades after emitting the instruction `a` describes (not resolved: identity). -/
def upg (e : AEnv) : Nat → A → AEnv
  | 0, _ => e
  | n + 1, .sym y =>
    match e.getD y none with
    | some a => upg (dropAft y e) n a
    | none => dropAft y e
  | n + 1, .data τ k fs =>
    if τ == tyMInst then
      match miKinds k with
      | some ks => upgF e n fs ks
      | none => deadEnv e
    else e
  | _, _ => e

/-- Emit the instruction fields of a flag/side-effect value in order. -/
def emitSeq (e : AEnv) (n : Nat) : List A → List SK → Option AEnv
  | f :: fs, .i :: ss => if fitsMI e n f then emitSeq (upg e n f) n fs ss else none
  | _ :: fs, _ :: ss => emitSeq e n fs ss
  | [], [] => some e
  | _, _ => none

/-- The non-instruction fields of a flag/side-effect value: results clean after the emission
(`e'`, real registers iff `z`), others clean before (`e`). -/
def restOk (e e' : AEnv) (n : Nat) (z : Bool) : List A → List SK → Bool
  | f :: fs, s :: ss =>
    (match s with
     | .i => true
     | .r => fitsCl e' n false z f
     | .o => fitsCl e n false true f) && restOk e e' n z fs ss
  | [], [] => true
  | _, _ => false

/-- A flag/side-effect value of shape `sh` with fields `fs`. -/
def flagOk (e : AEnv) (n : Nat) (z : Bool) (fs : List A) (sh : List SK) : Bool :=
  match emitSeq e n fs sh with
  | some e' => restOk e e' n z fs sh
  | none => false

/-- `a` fits the type predicate of `τ` (real result registers iff `z`). -/
def fitsTy (e : AEnv) : Nat → A → TypeId → Bool → Bool
  | 0, _, _, _ => false
  | n + 1, a, τ, z =>
    if τ == tyMInst then fitsMI e n a
    else if ciTys.contains τ then fitsCI e n a
    else match res e n a with
    | .ty τ' z' => τ' == τ && (!z' || z)
    | .cl false z' => !z' || z
    | .data τ' k fs =>
      τ' == τ && (match flagShape τ k with
      | some sh => flagOk e n z fs sh
      | none => match crShape τ k with
        | some cs => crOk e n z fs cs
        | none => false)
    | _ => false
where
  /-- The fields of a `CondResult` value. -/
  crOk (e : AEnv) (n : Nat) (z : Bool) : List A → List Bool → Bool
    | f :: fs, c :: cs =>
      (if c then fitsTy e n f TyId.«ProducesFlags» z else fitsCl e n false z f) &&
        crOk e n z fs cs
    | [], [] => true
    | _, _ => false

/-- `a` fits the summary `b` (`top`, `cl`, `wr` or `ty`). -/
def fitsA (e : AEnv) (n : Nat) (a : A) : A → Bool
  | .top => true
  | .cl b z => fitsCl e n b z a
  | .wr z => fitsWr e n z a
  | .ty τ z => fitsTy e n a τ z
  | _ => false

/-- `fitsA` pointwise. -/
def fitsAL (e : AEnv) (n : Nat) : List A → List A → Bool
  | a :: as, b :: bs => fitsA e n a b && fitsAL e n as bs
  | [], [] => true
  | _, _ => false

/-! ## Patterns -/

/-- The variable a pattern binds at its top. -/
def binder : Pattern → Option Nat
  | .bind _ x _ => some x
  | _ => none

/-- A field pattern that binds the field (or nothing) and checks nothing. -/
def simplePat : Pattern → Bool
  | .bind _ _ (.wildcard _) => true
  | .wildcard _ => true
  | _ => false

/-- The positions of the instruction fields before position `j`. -/
def instIdx (sh : List SK) (j : Nat) : List Nat :=
  (List.range j).filter fun i => sh[i]? == some SK.i

/-- The binders of the instruction fields before position `j`. -/
def instBinders (sh : List SK) (ps : List Pattern) (j : Nat) : List (Option Nat) :=
  (instIdx sh j).map fun i => ps[i]?.bind binder

/-- The relational abstract values of the fields of a flag/side-effect variant of shape `sh`
matched by patterns `ps`. -/
def relField (z : Bool) (sh : List SK) (ps : List Pattern) (j : Nat) : SK → A
  | .i =>
    let bs := instBinders sh ps j
    if bs.isEmpty then .ty tyMInst false
    else if bs.all (·.isSome) then .aft (bs.filterMap id) (.ty tyMInst false) else .top
  | .r =>
    let bs := instBinders sh ps j
    if instIdx sh sh.length == instIdx sh j && bs.all (·.isSome) then
      (if bs.isEmpty then .cl false z else .aft (bs.filterMap id) (.cl false z))
    else .top
  | .o => .cl false true

/-- The abstract fields of a value `a` describes, matched as variant `k` of `pty` (`enum`: by an
enum variant pattern, which checks the variant; a struct pattern does not). -/
def aun (e : AEnv) (a : A) (pty k : Nat) (enum : Bool) (ps : List Pattern) : List A :=
  match res e F a with
  | .cl b z => List.replicate ps.length (.cl b z)
  | .data _ k' fs => if k == k' then fs else List.replicate ps.length .top
  | .ty τ z =>
    if enum && τ == pty then
      match flagShape τ k with
      | some sh =>
        if ps.all simplePat then (List.range sh.length).map fun j => relField z sh ps j (sh.getD j .o)
        else List.replicate ps.length .top
      | none => match crShape τ k with
        | some cs => cs.map fun c => if c then .ty TyId.«ProducesFlags» z else .cl false z
        | none => List.replicate ps.length .top
    else List.replicate ps.length .top
  | _ => List.replicate ps.length .top

/-- The abstract outputs of extern extractor `id` on an input `a` describes. -/
def aext (e : AEnv) (id : TermId) (a : A) : A :=
  if (tyPred id).isSome || Flow.clean0Ext.contains id then .cl false false
  else if Flow.valueExt.contains id || id == TId.inst_data_value then
    (if fitsCl e F true true a then .cl false false else .top)
  else if id == TId.first_result then (if fitsCl e F false true a then .cl false false else .top)
  else .cl false false

section Prog
variable (p : Program)

mutual
/-- Bind the variables of `q` matched against a value `a` describes (`none`: a check failed:
a variable bound twice). -/
def aPat (a : A) : Pattern → AEnv → Option AEnv
  | .bind _ x sub, e =>
    match e[x]? with
    | some none => aPat a sub (e.set x (some a))
    | _ => none
  | .and _ ps, e => aPatAll a ps e
  | .term ty t args, e =>
    match p.term? t with
    | some term =>
      match term.kind with
      | .enumVariant k => aPatArgs (aun e a ty k true args) args e
      | .struct => aPatArgs (aun e a ty 0 false args) args e
      | .decl _ _ (some (.external _ _)) =>
        aPatArgs (List.replicate args.length (aext e term.id a)) args e
      | _ => some e
    | none => some e
  | _, e => some e
/-- `aPat` of every pattern, against the same value. -/
def aPatAll (a : A) : List Pattern → AEnv → Option AEnv
  | [], e => some e
  | q :: qs, e => match aPat a q e with
    | some e' => aPatAll a qs e'
    | none => none
/-- `aPat` pointwise (`top` past the end). -/
def aPatArgs : List A → List Pattern → AEnv → Option AEnv
  | as, q :: qs, e => match aPat (as.headD .top) q e with
    | some e' => aPatArgs as.tail qs e'
    | none => none
  | _, [], e => some e
end

/-! ## Terms -/

/-- The black-box oracle terms (hand-proved transfers): the emission of side effects. -/
def oracles : List TermId := [TId.«emit_side_effect», TId.«side_effect»]

/-- The pattern of a parameter bound to a variable. -/
def bindWild : Pattern → Option Nat
  | .bind _ x (.wildcard _) => some x
  | _ => none

/-- Constructor trees: enum variants and structs over parameter indices. -/
inductive CT where
  | leaf (i : Nat)
  | node (ty : TypeId) (k : Nat) (cs : List CT)
  deriving Repr, Inhabited

/-- The variant index of a data term. -/
def dataK? (t : TermId) : Option Nat :=
  match p.term? t with
  | some term => match term.kind with
    | .enumVariant k => some k
    | .struct => some 0
    | _ => none
  | none => none

mutual
/-- The constructor tree of an expression over the parameters `xs`. -/
def ctOf (xs : List Nat) : Isle.Expr → Option CT
  | .var _ x => (xs.idxOf? x).map CT.leaf
  | .term ty v es =>
    match dataK? p v, ctOfL xs es with
    | some k, some cs => some (.node ty k cs)
    | _, _ => none
  | _ => none
/-- `ctOf` of a list. -/
def ctOfL (xs : List Nat) : List Isle.Expr → Option (List CT)
  | [] => some []
  | e :: es => match ctOf xs e, ctOfL xs es with
    | some c, some cs => some (c :: cs)
    | _, _ => none
end

/-- A term whose only rule builds a constructor tree from its parameters. -/
def wrapper (t : TermId) : Option CT :=
  match p.rulesOf t with
  | [r] =>
    if r.iflets.isEmpty then
      match r.args.mapM bindWild with
      | some xs => if xs.Nodup then ctOf p xs r.rhs else none
      | none => none
    else none
  | _ => none

mutual
/-- A constructor tree over abstract arguments. -/
def ctA (as : List A) : CT → A
  | .leaf i => as.getD i .top
  | .node ty k cs => .data ty k (ctAL as cs)
/-- `ctA` of a list. -/
def ctAL (as : List A) : List CT → List A
  | [] => []
  | c :: cs => ctA as c :: ctAL as cs
end

/-- The extern constructors the embedding does not model (their calls never return). -/
def unmodeledCtors : List TermId := [TId.abi_dynamic_stackslot_addr]

/-- The extern constructors whose results are the join of their arguments' descriptions. -/
def genericCl (e : AEnv) (as : List A) : A :=
  if fitsCl.fitsClL e F true true as then
    .cl (!fitsCl.fitsClL e F false true as) (!fitsCl.fitsClL e F true false as)
  else .top

/-- The transfer of extern constructor `id` (`none`: its precondition fails). -/
def actor (e : AEnv) (id : TermId) (as : List A) : Option (A × AEnv) :=
  if id == TId.temp_writable_reg || id == TId.gen_call_output then some (.wr false, e)
  else if id == TId.invalid_reg then some (.top, e)
  else if unmodeledCtors.contains id then some (.cl false false, deadEnv e)
  else if id == TId.writable_reg_to_reg then some (as.headD .top, e)
  else if id == TId.value_reg || id == TId.value_regs then some (.regs as, e)
  else if id == TId.zero_reg || id == TId.writable_zero_reg then some (.cl false true, e)
  else if id == TId.emit then
    match res e F (as.headD .top) with
    | .data τ k _ =>
      if τ == tyMInst && (miKinds k).isNone then some (.cl false false, deadEnv e)
      else if fitsMI e F (as.headD .top) then some (.cl false false, upg e F (as.headD .top))
      else none
    | _ => if fitsMI e F (as.headD .top) then some (.cl false false, upg e F (as.headD .top))
      else none
  else if id == TId.load_constant_full || id == TId.opportunistic_def then some (.cl false false, e)
  else if id == TId.put_in_reg || id == TId.put_in_regs || id == TId.put_in_regs_vec ||
      id == TId.put_extended_in_reg then
    if fitsCl.fitsClL e F true true as then some (.cl false false, e) else some (.top, e)
  else if id == TId.abi_stackslot_addr then
    some (.data tyMInst VIdx.MInst.LoadAddr [as.headD .top, .cl false false], e)
  else if id == TId.gen_call_rets then
    match as with
    | [_, .sym x] => if fitsWr e F false (.sym x) then some (.crl [x], e) else some (.top, e)
    | _ => some (.top, e)
  else if id == TId.gen_try_call_rets then some (.crl [], e)
  else if id == TId.gen_call_info || id == TId.gen_call_ind_info then
    match as with
    | _ :: a1 :: u :: r :: _ =>
      if (id == TId.gen_call_info || fitsCl e F true true a1) && fitsCl e F true true u then
        match res e F r with
        | .crl xs => some (.cinfo xs, e)
        | _ => if fitsCl e F true true r then some (.ty TyId.«BoxCallInfo» false, e) else none
      else none
    | _ => none
  else if id == TId.gen_return || id == TId.gen_call_args then
    if fitsCl.fitsClL e F true true as then some (.cl false false, e) else none
  else some (genericCl e as, e)

/-- The transfer of an oracle term (`emit_side_effect`, `side_effect`): emit the instructions
of a side effect. -/
def aOracle (e : AEnv) (as : List A) : Option (A × AEnv) :=
  let a := as.headD .top
  if fitsTy e F a TyId.«SideEffectNoResult» true then
    match res e F a with
    | .data τ k fs =>
      match flagShape τ k with
      | some sh => (emitSeq e F fs sh).map fun e' => (.cl false false, e')
      | none => some (.cl false false, e)
    | _ => some (.cl false false, e)
  else none

/-- The internal terms whose results may hold real registers (`zero_reg`) when their arguments
may (with arguments without real registers, no result has one). -/
def zp : List TermId :=
  [172, 189, 249, 251, 254, 255, 257, 410, 559, 561, 562, 563, 574, 575, 576, 577, 578, 584, 625,
   626, 627, 649, 652, 653, 659, 660, 715, 717]

/-- Abstract application of term `t` (call-site type `ty`). -/
def aApply (ty : TypeId) (t : TermId) (as : List A) (e : AEnv) : Option (A × AEnv) :=
  match p.term? t with
  | some term =>
    match term.kind with
    | .enumVariant k => some (.data ty k as, e)
    | .struct => some (.data ty 0 as, e)
    | .decl _ (some (.external _)) _ => actor e t as
    | .decl _ (some .internal) _ =>
      if oracles.contains t then aOracle e as
      else match wrapper p t with
      | some c => some (ctA as c, e)
      | none =>
        if fitsAL e F as (term.args.map (tyA false)) then
          some (tyA false term.ret, e)
        else if fitsAL e F as (term.args.map (tyA true)) then
          some (tyA (zp.contains t) term.ret, e)
        else none
    | _ => none
  | none => none

mutual
/-- The variables an abstract value mentions. -/
def mentions : A → List Nat
  | .sym x => [x]
  | .aft ys a => ys ++ mentions a
  | .data _ _ fs => mentionsL fs
  | .regs as => mentionsL as
  | .crl xs | .cinfo xs => xs
  | _ => []
/-- `mentions` of a list. -/
def mentionsL : List A → List Nat
  | [] => []
  | a :: as => mentions a ++ mentionsL as
end

/-- No entry of `e` mentions a variable of `xs`. -/
def noMention (xs : List Nat) (e : AEnv) : Bool :=
  e.all fun o => match o with
    | some b => (mentions b).all fun y => !xs.contains y
    | none => true

/-- Variable `x` is unbound in `e`. -/
def unboundAt (e : AEnv) (x : Nat) : Bool :=
  match e[x]? with
  | some none => true
  | _ => false

/-- Unbind the variables `xs`. -/
def unbind (e : AEnv) : List Nat → AEnv
  | [] => e
  | x :: xs => unbind (e.set x none) xs

/-- Leaving a `let` of type `ty` binding `xs`: its variables become unbound (no other entry may
mention them), and its value is described by the type's summary. -/
def letClose (ty : TypeId) (xs : List Nat) (a : A) (e : AEnv) : Option (A × AEnv) :=
  if noMention xs (unbind e xs) then
    if fitsA e F a (tyA false ty) then some (tyA false ty, unbind e xs)
    else if fitsA e F a (tyA true ty) then some (tyA true ty, unbind e xs)
    else none
  else none

mutual
/-- Abstract evaluation of an expression: its value and the environment after it. -/
def aExpr : Isle.Expr → AEnv → Option (A × AEnv)
  | .var _ x, e => match e[x]? with
    | some (some _) => some (.sym x, e)
    | _ => none
  | .constBool .., e | .constInt .., e | .constPrim .., e => some (.cl false false, e)
  | .let ty bs body, e =>
    if (bs.map (·.1)).all (unboundAt e) then
      match aBinds bs e with
      | some e' => match aExpr body e' with
        | some (a, e'') => letClose ty (bs.map (·.1)) a e''
        | none => none
      | none => none
    else none
  | .term ty t args, e => match aArgs args e with
    | some (as, e') => aApply p ty t as e'
    | none => none
/-- Abstract evaluation of arguments, left to right. -/
def aArgs : List Isle.Expr → AEnv → Option (List A × AEnv)
  | [], e => some ([], e)
  | x :: xs, e => match aExpr x e with
    | some (a, e1) => match aArgs xs e1 with
      | some (as, e2) => some (a :: as, e2)
      | none => none
    | none => none
/-- Abstract `let*` bindings (each variable bound once). -/
def aBinds : List (VarId × TypeId × Isle.Expr) → AEnv → Option AEnv
  | [], e => some e
  | (x, _, ex) :: bs, e => match aExpr ex e with
    | some (a, e1) => match e1[x]? with
      | some none => aBinds bs (e1.set x (some a))
      | _ => none
    | none => none
end

/-- Abstract if-lets. -/
def aIfLets : List IfLet → AEnv → Option AEnv
  | [], e => some e
  | il :: ils, e => match aExpr p il.rhs e with
    | some (a, e1) => match aPat p a il.lhs e1 with
      | some e2 => aIfLets ils e2
      | none => none
    | none => none

/-- Rule `r` checks with argument descriptions `ins` and result summary `out`. -/
def aRule (ins : List A) (out : A) (r : Rule) : Bool :=
  match aPatArgs p ins r.args (List.replicate r.vars.length none) with
  | some e0 => match aIfLets p r.iflets e0 with
    | some e1 => match aExpr p r.rhs e1 with
      | some (a, e2) => fitsA e2 F a out
      | none => false
    | none => false
  | none => false

/-- The summary of term `t` for arguments with real registers iff `z`. -/
def termSum (z : Bool) (t : TermId) : List A × A :=
  match p.term? t with
  | some term => (term.args.map (tyA z), tyA (z && zp.contains t) term.ret)
  | none => ([], .top)

end Prog

/-! ## The closure -/

/-- Worklist closure under `Isle.ruleTerms` of the terms whose rules are checked. -/
def defClose : Nat → List TermId → Std.HashSet TermId → Std.HashSet TermId
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | k + 1, t :: ts, seen =>
    if seen.contains t then defClose k ts seen
    else if oracles.contains t || (wrapper program t).isSome then defClose k ts (seen.insert t)
    else defClose k ((program.rulesOf t).flatMap ruleTerms ++ ts) (seen.insert t)

/-- The root rules of `lower` checked by hand: `nop` (587) and the I128 rules 636, 637 (never
match a statement). -/
def defExcl : List RuleId := [587, 636, 637]

/-- The terms the root rules apply. -/
def defRoots : List TermId :=
  ((program.rulesOf TId.lower).filter fun r => !defExcl.contains r.id).flatMap ruleTerms ++
    (program.rulesOf TId.lower_branch).flatMap ruleTerms

/-- **The terms of the runs.** -/
def defTab : List TermId := (defClose 10000000 (oracles ++ defRoots) {}).toList

end Backend.Proof.DefGen
