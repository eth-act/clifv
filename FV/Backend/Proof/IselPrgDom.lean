import FV.Backend.Isel
import FV.Compile.Subset

/-!
# Progress of the ISLE lowering (V7): the abstract domain

The ISLE runs of the driver (`lower`/`lower_branch`, `FV/Backend/Isel.lean`) never fail on input
in scope: no interpreter error (an unmodeled helper call or constant, a value of the wrong shape,
an infallible helper failing, a total term without a matching rule, running out of fuel) and the
root returns a value. This is decided once over the exported rule data by an abstract
interpretation (`IselPrgCheck`) whose abstract values `PA` describe ISLE values **by shape**
(`γ`): unlike V3's coverage domain (`Cov.AW`), every abstract value but `any` fixes the
constructor of the values it describes, so that the checker can see that a pattern, an extern
helper or a constructor never meets a value it does not handle.

* `int lo hi`: an integer between the bounds that are given; `bool b`: a boolean, exactly `b`
  if given;
* `ty ts`: a type of `ts`;
* `inst t d`: an instruction of the context whose first result type `t` describes and whose
  `InstructionData` `d` describes (its results have types);
* `val ts`: a CLIF value of the context with a type in `ts`; `vals as`: a value list with one
  value per `as`; `valsMin lo`: a list of at least `lo` values with types;
* `reg`, `regs n`, `regsVec n`: a register, `n` registers, single-register entries (`n` of them
  if given); `label`, `labels lo n`, `blockCalls n`;
* `data t k fs`: variant `k` of type `t` with fields `fs`; `alts as`: one of `as`;
* `idata`: the `InstructionData` of an E instruction of the function;
* `op k n`: an operand of kind `k` (`OpOk`: e.g. a stack slot the frame has, a function
  reference to a declared callee with a supported signature, `n` its ABI returns; for the
  exception table of a `try_call` in its lowering context (`exnTry`), `n` its item count; the
  float immediates `fpModImm`/`movModImm` of the typed scope's float constants);
* `any`: no information; `bot`: no value.
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Aarch64

/-! ## Abstract values -/

/-- The kinds of operand values (`V.op`). -/
inductive OK where
  | imm12 | immLogic | immShift | uimm5 | uimm6 | simm9 | uimm12Scaled | shiftAmt | mwc | nzcv
  | memFlags | trapCode | stackSlot | funcRef | funcRefTry | globalValue | tlsGlobalValue | sig | sigTry
  | extName | callArgs | callRets | callInfo | extended | jumpTable | tryCallNone | exnTable
  | exnTry | tryCallInfo | unit | fpModImm | movModImm
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

/-- Abstract ISLE values (meaning: `γ`). -/
inductive PA where
  | bot
  | any
  | int (lo hi : Option Int)
  | bool (b : Option Bool)
  | ty (ts : List CTy)
  | inst (t : PA) (d : PA)
  | val (ts : List CTy)
  | vals (as : List PA)
  | valsMin (lo : Nat)
  | reg
  | regs (n : Nat)
  | regsVec (n : Option Nat)
  | label
  | labels (lo : Nat) (n : Option Nat)
  | blockCalls (n : Nat)
  | data (t : TypeId) (k : Nat) (fs : List PA)
  | alts (as : List PA)
  | idata
  | op (k : OK) (n : Option Nat)
  deriving Repr, Inhabited

/-- Abstract environments: per rule variable, its abstract value once bound. -/
abbrev AEnv := List (Option PA)

/-! ## The meaning -/

/-- The signatures the lowering of a call handles: `sigArgLocs` succeeds and at most 8 ABI
returns (`retRegs`). -/
def SigOk (s : Clif.Signature) : Prop :=
  (∃ r, sigArgLocs s = .ok r) ∧ (sigRets s).length ≤ 8

/-- `s` has `n` ABI returns, if `n` is given. -/
def RetsN (n : Option Nat) (s : Clif.Signature) : Prop :=
  n = none ∨ n = some (sigRets s).length

/-- `f`'s statement instruction `c`. -/
def InstOf (f : Clif.Function) (c : Clif.Inst) : Prop :=
  ∃ B ∈ f.blocks, ∃ s ∈ B.body, s.inst = c

section
variable (f : Clif.Function) (ctx : Ctx)

/-- **The meaning of an operand leaf** `op k n`. -/
def OpOk : OK → Option Nat → Opnd → Prop
  | .imm12, _, o => ∃ i, o = .imm12 i
  | .immLogic, _, o => ∃ i, o = .immLogic i
  | .immShift, _, o => ∃ s, o = .immShift s ∧ s < 64
  | .uimm5, _, o => ∃ s, o = .uimm5 s
  | .uimm6, _, o => ∃ s, o = .uimm6 s
  | .simm9, _, o => ∃ i, o = .simm9 i
  | .uimm12Scaled, _, o => ∃ i, o = .uimm12Scaled i
  | .shiftAmt, _, o => ∃ s, o = .shiftOpAndAmt s
  | .mwc, _, o => ∃ m, o = .moveWideConst m
  | .nzcv, _, o => ∃ x, o = .nzcv x
  | .memFlags, _, o => ∃ x, o = .memFlags x ∧ x.endianness ≠ some .big
  | .trapCode, _, o => ∃ c, o = .trapCode c
  | .stackSlot, _, o => ∃ s, o = .stackSlot s ∧ (ctx.slotOff.lookup s).isSome
  | .funcRef, n, o => ∃ fn ext, o = .funcRef fn ∧ ctx.func.extern? fn = some ext ∧
      SigOk ext.sig ∧ RetsN n ext.sig
  | .funcRefTry, _, o => ∃ fn ext, o = .funcRef fn ∧ ctx.func.extern? fn = some ext ∧
      SigOk ext.sig ∧ ctx.tryRegs.1.length = (sigRets ext.sig).length
  | .globalValue, _, o => ∃ g name off col, o = .globalValue g ∧
      ctx.func.globals.lookup g = some (.symbol name off col)
  | .tlsGlobalValue, _, o => ∃ g name off col, o = .tlsGlobalValue g ∧
      ctx.func.globals.lookup g = some (.tlsSymbol name off col)
  | .sig, n, o => ∃ s, o = .sig s ∧ SigOk s ∧ RetsN n s
  | .sigTry, _, o => ∃ s, o = .sig s ∧ SigOk s ∧ ctx.tryRegs.1.length = (sigRets s).length
  | .extName, _, o => ∃ x, o = .extName x
  | .callArgs, _, o => ∃ x, o = .callArgs x
  | .callRets, _, o => ∃ x, o = .callRets x
  | .callInfo, _, o => ∃ x, o = .callInfo x
  | .extended, _, o => ∃ x e, o = .extended x e ∧ (ctx.valueReg? x).isSome
  | .jumpTable, _, o => ∃ x, o = .jumpTable x
  | .tryCallNone, _, o => o = .tryCallNone
  | .exnTable, n, o => ∃ s items, o = .exnTable s items ∧ SigOk s ∧ RetsN n s
  | .exnTry, n, o => ∃ s items, o = .exnTable s items ∧ SigOk s ∧
      ctx.tryRegs.1.length = (sigRets s).length ∧ (n = none ∨ n = some items.length)
  | .tryCallInfo, _, o => ∃ x, o = .tryCallInfo x
  | .fpModImm, _, o => ∃ i, o = .fpModImm i
  | .movModImm, _, o => ∃ i, o = .movModImm i
  | .unit, _, o => o = .unit

mutual
/-- **The meaning of an abstract value.** -/
def γ : PA → V → Prop
  | .bot, _ => False
  | .any, _ => True
  | .int lo hi, v => ∃ i, v = .int i ∧ (∀ l, lo = some l → l ≤ i) ∧ (∀ h, hi = some h → i ≤ h)
  | .bool b, v => ∃ x, v = .bool x ∧ (b = none ∨ b = some x)
  | .ty ts, v => ∃ t ∈ ts, v = .ty t
  | .inst t d, v => ∃ j info, v = .inst j ∧ ctx.insts[j]? = some info ∧
      γ t (.ty (info.resTys.head?.getD .invalid)) ∧ γ d info.data ∧
      ∀ r ∈ info.results, (ctx.valueType? r).isSome
  | .val ts, v => ∃ x t, v = .value x ∧ ctx.valueType? x = some t ∧ t ∈ ts
  | .vals as, v => ∃ xs, v = .values xs ∧ γL as (xs.map .value)
  | .valsMin lo, v => ∃ xs, v = .values xs ∧ lo ≤ xs.length ∧ ∀ x ∈ xs, (ctx.valueType? x).isSome
  | .reg, v => ∃ r, v = .reg r
  | .regs n, v => ∃ rs, v = .regs rs ∧ rs.length = n
  | .regsVec n, v => ∃ rss, v = .regsVec rss ∧ (∀ rs ∈ rss, rs.length = 1) ∧
      (n = none ∨ n = some rss.length)
  | .label, v => ∃ l, v = .label l
  | .labels lo n, v => ∃ ls, v = .labels ls ∧ lo ≤ ls.length ∧ (n = none ∨ n = some ls.length)
  | .blockCalls n, v => ∃ bs, v = .blockCalls bs ∧ bs.length = n
  | .data t k fs, v => ∃ ws, v = .data t k ws ∧ γL fs ws
  | .alts as, v => γAny as v
  | .idata, v => ∃ c, InstOf f c ∧ Compile.instE c = true ∧ instData f c = .ok v
  | .op k n, v => ∃ o, v = .op o ∧ OpOk ctx k n o
/-- Some abstract value of the list describes `v`. -/
def γAny : List PA → V → Prop
  | [], _ => False
  | a :: as, v => γ a v ∨ γAny as v
/-- Pointwise `γ` (same lengths). -/
def γL : List PA → List V → Prop
  | [], [] => True
  | a :: as, v :: vs => γ a v ∧ γL as vs
  | _, _ => False
end

/-- An abstract environment describes an interpreter environment: the same size, and every
bound abstract variable is bound to a value it describes. -/
def EnvOK (aenv : AEnv) (env : Isle.Interp.Env V) : Prop :=
  env.size = aenv.length ∧
    ∀ (x : Nat) (a : PA), aenv[x]? = some (some a) → ∃ v, env[x]? = some (some v) ∧ γ f ctx a v

end

/-! ## The order -/

namespace PA

/-- The value lists `valsMin` describes: every element a `val`. -/
def isVal : PA → Bool
  | .val _ => true
  | .bot => true
  | _ => false

/-- **The order** at recursion depth `n` (`false` when the depth runs out): every value `a`
describes, `b` describes (`le_sound`). By recursion on the depth, so that the kernel evaluates it
when the table is checked. -/
def leF : Nat → PA → PA → Bool
  | 0, _, _ => false
  | n + 1, a, b =>
    match a, b with
    | .bot, _ => true
    | _, .any => true
    | .alts as, b => as.all fun x => leF n x b
    | a, .alts bs => bs.any fun y => leF n a y
    | .int lo hi, .int lo' hi' =>
      (match lo' with
       | none => true
       | some l' => match lo with | some l => decide (l' ≤ l) | none => false) &&
      (match hi' with
       | none => true
       | some h' => match hi with | some h => decide (h ≤ h') | none => false)
    | .bool c, .bool d => d.isNone || c == d
    | .ty ts, .ty us => ts.all (us.contains ·)
    | .inst t d, .inst t' d' => leF n t t' && leF n d d'
    | .val ts, .val us => ts.all (us.contains ·)
    | .vals as, .vals bs => as.length == bs.length && (as.zip bs).all fun q => leF n q.1 q.2
    | .vals as, .valsMin lo => decide (lo ≤ as.length) && as.all isVal
    | .valsMin lo, .valsMin lo' => decide (lo' ≤ lo)
    | .reg, .reg => true
    | .regs n₁, .regs m => n₁ == m
    | .regsVec n₁, .regsVec m => m.isNone || n₁ == m
    | .label, .label => true
    | .labels lo k, .labels lo' k' =>
      match k with
      | some j => decide (lo' ≤ j) && (k'.isNone || k' == some j)
      | none => decide (lo' ≤ lo) && k'.isNone
    | .blockCalls n₁, .blockCalls m => n₁ == m
    | .data t k fs, .data t' k' gs =>
      t == t' && k == k' && fs.length == gs.length && (fs.zip gs).all fun q => leF n q.1 q.2
    | .idata, .idata => true
    | .op k m, .op k' m' => k == k' && (m'.isNone || m == m')
    | _, _ => false

/-- **The order** (`leF` at depth 64, far above the depth of the table's values). -/
def le (a b : PA) : Bool := leF 64 a b

/-- Pointwise order (same lengths). -/
def leL (as bs : List PA) : Bool := as.length == bs.length && (as.zip bs).all fun q => le q.1 q.2

/-- An abstract value no value has (pruned). -/
def isBot : PA → Bool
  | .bot => true
  | .ty [] => true
  | .val [] => true
  | .alts [] => true
  | _ => false

mutual
/-- Split a value into finitely many cases (for the exhaustiveness check): a set of types or of
typed values into singletons, alternatives into their members, an unknown boolean into both,
and the parts of an instruction, of data and of a value list. -/
def split : PA → List PA
  | .ty ts => ts.map fun t => .ty [t]
  | .val ts => ts.map fun t => .val [t]
  | .alts as => as
  | .bool none => [.bool (some false), .bool (some true)]
  | .inst t d => (split t).flatMap fun t' => (split d).map (.inst t' ·)
  | .data t k fs => (splitL fs).map (.data t k ·)
  | .vals as => (splitL as).map .vals
  | a => [a]
/-- The cases of an argument list: every combination of the arguments' cases. -/
def splitL : List PA → List (List PA)
  | [] => [[]]
  | a :: as => (split a).flatMap fun b => (splitL as).map (b :: ·)
end

end PA

end Backend.Proof.Prg
