import FV.Compile.Abi

/-!
# The DSL → CLIF emitter (`Compile.compile`)

Structurally recursive over the DSL AST, compositional, no global optimisation. Code is
generated in a state monad `CGM` that threads the fresh-name supply (values, blocks, stack
slots), the extern declarations, the finished blocks, and the block under construction.

Conventions (see `docs/contracts/compile.md` §3 and §6):

* A compile-time environment `env : List (List ValueId)` has one entry per DSL variable of the
  context `Γ` (index = `Var.idx`); entry `i` lists the SSA values holding `flat` of variable
  `i`'s value.
* `compileExpr`/`compileOp` emit into the current block (possibly ending it and continuing in
  fresh blocks) and return the values holding the result.
* `compileStmt` always ends the current block. Its result goes to a continuation `Cont`:
  return from the function, or jump to a join block with the result as block arguments.
* Every failure jumps to the function's error exit `block1(tag : i8)`, which returns `tag`
  with a zero payload. `block0` is the entry block.
-/

namespace Compile

open DSL (Ty IntW)
open Clif (ValueId BlockId SlotId FnRef Inst Terminator BlockCall)

/-- Where the value of a statement goes. -/
inductive Cont where
  /-- return `(0, value)` from the function -/
  | ret
  /-- jump to the join block with the value as block arguments -/
  | jump (b : BlockId)
  deriving DecidableEq, Repr

/-- Per-function constants. -/
structure FnCtx where
  abi : FnAbi
  /-- the runtime-context parameter, if the function takes one -/
  ctx : Option ValueId
  /-- the result-buffer parameter, in buffer mode -/
  retBuf : Option ValueId

/-- The error exit of every compiled function. -/
def errBlock : BlockId := 1

/-- Code-generator state. -/
structure CG where
  nextVal : Nat := 0
  nextBlock : Nat := 2
  slots : List (SlotId × Clif.StackSlot) := []
  externs : List (FnRef × Clif.ExtFunc) := []
  /-- finished blocks, most recent first -/
  done : List Clif.Block := []
  cur : BlockId := 0
  curParams : List (ValueId × Clif.Ty) := []
  /-- statements of the current block, most recent first -/
  curBody : List Clif.Stmt := []

abbrev CGM := StateM CG

/-! ## Primitive generator actions -/

def fresh : CGM ValueId :=
  modifyGet fun s => (s.nextVal, { s with nextVal := s.nextVal + 1 })

def freshFor (tys : List Clif.Ty) : CGM (List ValueId) := tys.mapM fun _ => fresh

def emitStmt (results : List ValueId) (inst : Inst) : CGM Unit :=
  modify fun s => { s with curBody := { results, inst } :: s.curBody }

/-- Emit a single-result instruction. -/
def inst1 (inst : Inst) : CGM ValueId := do
  let v ← fresh
  emitStmt [v] inst
  pure v

def iconstN (ty : Clif.Ty) (n : Nat) : CGM ValueId := inst1 (.iconst ty (BitVec.ofNat ty.width n))

def newBlock : CGM BlockId :=
  modifyGet fun s => (s.nextBlock, { s with nextBlock := s.nextBlock + 1 })

/-- End the current block with `t`. -/
def terminate (t : Terminator) : CGM Unit :=
  modify fun s =>
    { s with done := { id := s.cur, params := s.curParams, body := s.curBody.reverse, term := t } :: s.done
             curBody := [] }

/-- Continue emitting into block `b` with parameters `params`. -/
def switchTo (b : BlockId) (params : List (ValueId × Clif.Ty)) : CGM Unit :=
  modify fun s => { s with cur := b, curParams := params, curBody := [] }

/-- A fresh explicit stack slot of `size` bytes, 8-byte aligned. -/
def newSlot (size : Nat) : CGM SlotId :=
  modifyGet fun s =>
    let id := s.slots.length
    (id, { s with slots := s.slots ++ [(id, { size, align := some 8 })] })

/-- The function reference for callee `name` (declared once per function). -/
def declare (name : String) (sig : Clif.Signature) : CGM FnRef := do
  let s ← get
  match s.externs.find? (·.2.name == name) with
  | some (r, _) => pure r
  | none =>
    let r := s.externs.length
    set { s with externs := s.externs ++ [(r, ({ name, sig } : Clif.ExtFunc))] }
    pure r

/-- Emit a call; returns the result values. -/
def callFn (name : String) (sig : Clif.Signature) (args : List ValueId) : CGM (List ValueId) := do
  let r ← declare name sig
  let res ← freshFor (sig.returns.map (·.ty))
  emitStmt res (.call r args)
  pure res

/-- Branch to the error exit with `tag` if `c` is non-zero, else continue in a fresh block. -/
def errIf (c : ValueId) (tag : Nat) : CGM Unit := do
  let tv ← iconstN .i8 tag
  let ok ← newBlock
  terminate (.brif c ⟨errBlock, [tv]⟩ ⟨ok, []⟩)
  switchTo ok []

/-- `notrap aligned`: only for accesses to the function's own stack slots at offsets that are
multiples of 8 (slots are 8-byte aligned and sized for every access). -/
def slotFlags : Clif.MemFlags := { trapCode := none, aligned := true }

/-! ## Runtime externs (`docs/contracts/compile.md` §4): `ctx` is always the first argument -/

def rtSig (nparams : Nat) (ret : Option Clif.Ty) : Clif.Signature :=
  { params := List.replicate nparams { ty := .i64 }, returns := ret.toList.map fun t => { ty := t } }

def rtNew : String × Clif.Signature := ("flat_map_new", rtSig 1 (some .i64))
def rtInsert : String × Clif.Signature := ("flat_map_insert", rtSig 4 none)
def rtContains : String × Clif.Signature := ("flat_map_contains", rtSig 3 (some .i8))
def rtGet : String × Clif.Signature := ("flat_map_get", rtSig 4 (some .i8))
def rtClone : String × Clif.Signature := ("flat_map_clone", rtSig 2 (some .i64))
def rtLen : String × Clif.Signature := ("flat_map_len", rtSig 2 (some .i64))
def rtEntry : String × Clif.Signature := ("flat_map_entry", rtSig 5 none)

def callRt (rt : String × Clif.Signature) (args : List ValueId) : CGM (List ValueId) :=
  callFn rt.1 rt.2 args

/-! ## Scalar helpers -/

def IBin.clif : DSL.IBin → Clif.BinaryOp
  | .add => .iadd | .sub => .isub | .mul => .imul | .and => .band | .or => .bor
  | .xor => .bxor | .shl => .ishl | .lshr => .ushr | .ashr => .sshr

def ICmp.clif : DSL.ICmp → Clif.IntCC
  | .eq => .eq | .ne => .ne | .ult => .ult | .ule => .ule | .slt => .slt | .sle => .sle

/-- A map key/value (`int`/`bool`, one value) zero-extended to an `i64` word. -/
def toWordV : Ty → List ValueId → CGM ValueId
  | .int .w64, vs => pure (vs.headD 0)
  | .int _, vs => inst1 (.extend .uextend .i64 (vs.headD 0))
  | .bool, vs => inst1 (.extend .uextend .i64 (vs.headD 0))
  | _, _ => iconstN .i64 0

/-- The key/value representation of an `i64` word (inverse of `toWordV`). -/
def ofWordV : Ty → ValueId → CGM (List ValueId)
  | .int .w64, x => pure [x]
  | .int w, x => do pure [← inst1 (.ireduce (intTy w) x)]
  | .bool, x => do pure [← inst1 (.ireduce .i8 x)]
  | _, _ => pure []

/-- Values `[k·m, (k+1)·m)` of a flattened vector (element `k`, element size `m`). -/
def chunk (vs : List ValueId) (m k : Nat) : List ValueId := (vs.drop (k * m)).take m

/-- Error `indexOutOfBounds` unless `i <u n` (omitted when every `w`-bit index is `< n`). -/
def boundsCheck (w : IntW) (n : Nat) (i : ValueId) : CGM Unit :=
  if n < 2 ^ w.bits then do
    let nv ← iconstN (intTy w) n
    let c ← inst1 (.icmp .uge (intTy w) i nv)
    errIf c (DSL.Err.indexOutOfBounds.tag)
  else pure ()

/-- `select` by `brif` into a join block: the join's parameters hold `x` if `c`, else `y`. -/
def selectVals (tys : List Clif.Ty) (c : ValueId) (x y : List ValueId) : CGM (List ValueId) := do
  let j ← newBlock
  let ps ← freshFor tys
  terminate (.brif c ⟨j, x⟩ ⟨j, y⟩)
  switchTo j (ps.zip tys)
  pure ps

/-- Element `i` of the flattened vector `vs` (`n` elements of type `t`, index width `w`),
assuming `i <u n`: a chain `r := (i = k) ? elem k : r` for `k = 1 … n-1`, starting from
element 0. Positions not representable in `w` bits are unreachable and skipped. -/
def selectElem (t : Ty) (w : IntW) (n : Nat) (i : ValueId) (vs : List ValueId) :
    CGM (List ValueId) :=
  let m := (flat t).length
  (List.range n).tail.foldlM (init := chunk vs m 0) fun acc k =>
    if k < 2 ^ w.bits then do
      let kv ← iconstN (intTy w) k
      let c ← inst1 (.icmp .eq (intTy w) i kv)
      selectVals (flat t) c (chunk vs m k) acc
    else pure acc

/-- The flattened vector `vs` with element `i` replaced by `e`: per position `k`,
`elem k := (i = k) ? e : elem k`. -/
def updateElem (t : Ty) (w : IntW) (n : Nat) (i : ValueId) (e vs : List ValueId) :
    CGM (List ValueId) := do
  let m := (flat t).length
  let elems ← (List.range n).mapM fun k =>
    if k < 2 ^ w.bits then do
      let kv ← iconstN (intTy w) k
      let c ← inst1 (.icmp .eq (intTy w) i kv)
      selectVals (flat t) c e (chunk vs m k)
    else pure (chunk vs m k)
  pure elems.flatten

/-! ## Expressions -/

/-- Deep copy: maps are cloned by the runtime, everything else is an immutable SSA value. -/
def cloneVals (fc : FnCtx) : Ty → List ValueId → CGM (List ValueId)
  | .map _ _, vs => callRt rtClone [fc.ctx.getD 0, vs.headD 0]
  | .prod a b, vs => do
    let n := (flat a).length
    let x ← cloneVals fc a (vs.take n)
    let y ← cloneVals fc b (vs.drop n)
    pure (x ++ y)
  | .vec n t, vs =>
    if t.hasMap then do
      let m := (flat t).length
      let xs ← (List.range n).mapM fun k => cloneVals fc t (chunk vs m k)
      pure xs.flatten
    else pure vs
  | _, vs => pure vs

def compileExpr (fc : FnCtx) {Γ : List Ty} (env : List (List ValueId)) :
    {t : Ty} → DSL.Expr Γ t → CGM (List ValueId)
  | _, .var v => pure (env.getD v.idx [])
  | t, .clone v => cloneVals fc t (env.getD v.idx [])
  | _, .ilit w x => do pure [← iconstN (intTy w) x.toNat]
  | _, .blit b => do pure [← iconstN .i8 (if b then 1 else 0)]
  | _, .unit => pure []
  | _, .ibin (w := w) op a b => do
    let x ← compileExpr fc env a
    let y ← compileExpr fc env b
    pure [← inst1 (.binary (IBin.clif op) (intTy w) (x.headD 0) (y.headD 0))]
  | _, .inot (w := w) a => do
    let x ← compileExpr fc env a
    pure [← inst1 (.unary .bnot (intTy w) (x.headD 0))]
  | _, .icmp (w := w) op a b => do
    let x ← compileExpr fc env a
    let y ← compileExpr fc env b
    pure [← inst1 (.icmp (ICmp.clif op) (intTy w) (x.headD 0) (y.headD 0))]
  | _, .cast (w := w) op w' a => do
    let x := (← compileExpr fc env a).headD 0
    if w'.bits < w.bits then pure [← inst1 (.ireduce (intTy w') x)]
    else if w.bits < w'.bits then
      match op with
      | .sext => pure [← inst1 (.extend .sextend (intTy w') x)]
      | _ => pure [← inst1 (.extend .uextend (intTy w') x)]
    else pure [x]
  | _, .band a b => do
    let x ← compileExpr fc env a
    let y ← compileExpr fc env b
    pure [← inst1 (.binary .band .i8 (x.headD 0) (y.headD 0))]
  | _, .bor a b => do
    let x ← compileExpr fc env a
    let y ← compileExpr fc env b
    pure [← inst1 (.binary .bor .i8 (x.headD 0) (y.headD 0))]
  | _, .bnot a => do
    let x ← compileExpr fc env a
    let one ← iconstN .i8 1
    pure [← inst1 (.binary .bxor .i8 (x.headD 0) one)]
  | t, .cond c a b => do
    let cv ← compileExpr fc env c
    let x ← compileExpr fc env a
    let y ← compileExpr fc env b
    selectVals (flat t) (cv.headD 0) x y
  | _, .pair a b => do
    let x ← compileExpr fc env a
    let y ← compileExpr fc env b
    pure (x ++ y)
  | _, .fst (a := a) p => do
    let x ← compileExpr fc env p
    pure (x.take (flat a).length)
  | _, .snd (a := a) p => do
    let x ← compileExpr fc env p
    pure (x.drop (flat a).length)
  | _, .vrepl n a => do
    let x ← compileExpr fc env a
    pure (List.replicate n x).flatten
  | _, .mapEmpty => callRt rtNew [fc.ctx.getD 0]
  | _, .mapContains (k := kt) m key => do
    let kv ← compileExpr fc env key
    let kw ← toWordV kt kv
    callRt rtContains [fc.ctx.getD 0, (env.getD m.idx []).headD 0, kw]

def compileExprs (fc : FnCtx) {Γ : List Ty} (env : List (List ValueId)) :
    {σ : List Ty} → DSL.Exprs Γ σ → CGM (List ValueId)
  | _, .nil => pure []
  | _, .cons e es => do
    let x ← compileExpr fc env e
    let xs ← compileExprs fc env es
    pure (x ++ xs)

/-! ## Fallible operations -/

def compileOp (fc : FnCtx) {Γ : List Ty} (env : List (List ValueId)) :
    {t : Ty} → DSL.Op Γ t → CGM (List ValueId)
  | _, .iop (w := w) op a b => do
    let x := (← compileExpr fc env a).headD 0
    let y := (← compileExpr fc env b).headD 0
    let ty := intTy w
    match op with
    | .addC =>
      let s ← inst1 (.binary .iadd ty x y)
      let c ← inst1 (.icmp .ult ty s x)
      errIf c DSL.Err.overflow.tag
      pure [s]
    | .subC =>
      let d ← inst1 (.binary .isub ty x y)
      let c ← inst1 (.icmp .ult ty x y)
      errIf c DSL.Err.overflow.tag
      pure [d]
    | .mulC =>
      let p ← inst1 (.binary .imul ty x y)
      let hi ← inst1 (.binary .umulhi ty x y)
      let z ← iconstN ty 0
      let c ← inst1 (.icmp .ne ty hi z)
      errIf c DSL.Err.overflow.tag
      pure [p]
    | .udiv =>
      let z ← iconstN ty 0
      let c ← inst1 (.icmp .eq ty y z)
      errIf c DSL.Err.divByZero.tag
      pure [← inst1 (.div .udiv ty x y)]
    | .urem =>
      let z ← iconstN ty 0
      let c ← inst1 (.icmp .eq ty y z)
      errIf c DSL.Err.divByZero.tag
      pure [← inst1 (.div .urem ty x y)]
  | t, .vget (n := n) (w := w) v i => do
    let iv := (← compileExpr fc env i).headD 0
    boundsCheck w n iv
    selectElem t w n iv (env.getD v.idx [])
  | t, .mapGet (k := kt) m key => do
    let kw ← toWordV kt (← compileExpr fc env key)
    let slot ← newSlot 8
    let p ← inst1 (.stackAddr .i64 slot 0)
    let found := (← callRt rtGet [fc.ctx.getD 0, (env.getD m.idx []).headD 0, kw, p]).headD 0
    let tv ← iconstN .i8 DSL.Err.notFound.tag
    let ok ← newBlock
    terminate (.brif found ⟨ok, []⟩ ⟨errBlock, [tv]⟩)
    switchTo ok []
    let raw ← inst1 (.load .load .i64 slotFlags p 0)
    ofWordV t raw

/-! ## Statements -/

/-- Store flattened values into a result buffer (8 bytes per value). The buffer comes from the
caller, so the stores keep the default (trapping) flags. -/
def storeVals (p : ValueId) (tys : List Clif.Ty) (vs : List ValueId) : CGM Unit :=
  ((vs.zip tys).zip (List.range vs.length)).forM fun ((v, ty), j) =>
    emitStmt [] (.store .store ty {} v p (8 * j))

/-- Load flattened values from a result buffer in one of this function's stack slots. -/
def loadVals (p : ValueId) (tys : List Clif.Ty) : CGM (List ValueId) :=
  (tys.zip (List.range tys.length)).mapM fun (ty, j) => inst1 (.load .load ty slotFlags p (8 * j))

/-- Deliver a statement's value to its continuation. -/
def finish (fc : FnCtx) : Cont → List ValueId → CGM Unit
  | .jump b, vs => terminate (.jump ⟨b, vs⟩)
  | .ret, vs => do
    let t0 ← iconstN .i8 0
    match fc.retBuf with
    | some p =>
      storeVals p (flat fc.abi.result) vs
      terminate (.ret [t0])
    | none => terminate (.ret (t0 :: vs))

def compileStmt (fc : FnCtx) :
    {Γ : List Ty} → {τ : Ty} → List (List ValueId) → DSL.Stmt Γ τ → Cont → CGM Unit
  | _, _, env, .ret e, kont => do finish fc kont (← compileExpr fc env e)
  | _, _, _, .throw e, _ => do
    let tv ← iconstN .i8 e.tag
    terminate (.jump ⟨errBlock, [tv]⟩)
  | _, _, env, .op o, kont => do finish fc kont (← compileOp fc env o)
  | _, _, env, .call (τ := τ') name body args, kont => do
    let argv ← compileExprs fc env args
    let abi := bodyAbi body
    let buf ← if abi.sret then do
        let s ← newSlot abi.bufSize
        pure (some (← inst1 (.stackAddr .i64 s 0)))
      else pure none
    let ctxArg := if abi.ctx then [fc.ctx.getD 0] else []
    let res ← callFn (mangle name) abi.signature (ctxArg ++ buf.toList ++ argv)
    let tag := res.headD 0
    let ok ← newBlock
    terminate (.brif tag ⟨errBlock, [tag]⟩ ⟨ok, []⟩)
    switchTo ok []
    let payload ← match buf with
      | some p => loadVals p (flat τ')
      | none => pure res.tail
    finish fc kont payload
  | _, _, env, .let_ e s, kont => do
    let x ← compileExpr fc env e
    compileStmt fc (x :: env) s kont
  | _, _, env, .letPair (a := a) e s, kont => do
    let x ← compileExpr fc env e
    let n := (flat a).length
    compileStmt fc (x.drop n :: x.take n :: env) s kont
  | _, _, env, .bind (α := α) s k, kont => do
    let j ← newBlock
    let ps ← freshFor (flat α)
    compileStmt fc env s (.jump j)
    switchTo j (ps.zip (flat α))
    compileStmt fc (ps :: env) k kont
  | _, _, env, .set v e s, kont => do
    let x ← compileExpr fc env e
    compileStmt fc (env.set v.idx x) s kont
  | _, _, env, .vset (n := n) (α := α) (w := w) v i e s, kont => do
    let iv := (← compileExpr fc env i).headD 0
    let ev ← compileExpr fc env e
    boundsCheck w n iv
    let xs ← updateElem α w n iv ev (env.getD v.idx [])
    compileStmt fc (env.set v.idx xs) s kont
  | _, _, env, .mapInsert (k := kt) (val := vt) m key val s, kont => do
    let kw ← toWordV kt (← compileExpr fc env key)
    let vw ← toWordV vt (← compileExpr fc env val)
    let _ ← callRt rtInsert [fc.ctx.getD 0, (env.getD m.idx []).headD 0, kw, vw]
    compileStmt fc env s kont
  | _, _, env, .ite c t e, kont => do
    let cv := (← compileExpr fc env c).headD 0
    let bt ← newBlock
    let be ← newBlock
    terminate (.brif cv ⟨bt, []⟩ ⟨be, []⟩)
    switchTo bt []
    compileStmt fc env t kont
    switchTo be []
    compileStmt fc env e kont
  | _, _, env, .forRange (α := α) n init body, kont => do
    -- header(i, acc): i <u n ? body : exit;  body → latch(acc') → header(i + 1, acc')
    let x ← compileExpr fc env init
    let hdr ← newBlock
    let iP ← fresh
    let accP ← freshFor (flat α)
    let i0 ← iconstN .i64 0
    terminate (.jump ⟨hdr, i0 :: x⟩)
    switchTo hdr ((iP, .i64) :: accP.zip (flat α))
    let nv ← iconstN .i64 n
    let c ← inst1 (.icmp .ult .i64 iP nv)
    let bb ← newBlock
    let exit ← newBlock
    let latch ← newBlock
    terminate (.brif c ⟨bb, []⟩ ⟨exit, []⟩)
    switchTo bb []
    compileStmt fc (accP :: [iP] :: env) body (.jump latch)
    let accL ← freshFor (flat α)
    switchTo latch (accL.zip (flat α))
    let one ← iconstN .i64 1
    let i1 ← inst1 (.binary .iadd .i64 iP one)
    terminate (.jump ⟨hdr, i1 :: accL⟩)
    switchTo exit []
    finish fc kont accP

/-! ## Functions and programs -/

/-- Compile one function body into the CLIF function `%(mangle name)`. -/
def compileBody (name : String) {σ : List Ty} {τ : Ty} (body : DSL.Stmt σ τ) : Clif.Function :=
  let abi := bodyAbi body
  let gen : CGM Unit := do
    let ctxV ← if abi.ctx then some <$> fresh else pure none
    let bufV ← if abi.sret then some <$> fresh else pure none
    let argVals ← σ.mapM fun t => freshFor (flat t)
    let params := ctxV.toList.map (·, Clif.Ty.i64) ++ bufV.toList.map (·, Clif.Ty.i64) ++
      argVals.flatten.zip (flatList σ)
    switchTo 0 params
    let fc : FnCtx := { abi, ctx := ctxV, retBuf := bufV }
    compileStmt fc argVals body .ret
    -- the error exit: return the tag with a zero payload
    let tag ← fresh
    switchTo errBlock [(tag, .i8)]
    match bufV with
    | some p =>
      let zs ← (flat τ).mapM fun ty => iconstN ty 0
      storeVals p (flat τ) zs
      terminate (.ret [tag])
    | none =>
      let zs ← (flat τ).mapM fun ty => iconstN ty 0
      terminate (.ret (tag :: zs))
  let s := (gen.run {}).2
  { name := mangle name
    sig := abi.signature
    slots := s.slots
    externs := s.externs
    blocks := s.done.reverse }

/-- A callee embedded in a `Stmt.call`. -/
structure Callee where
  σ : List Ty
  τ : Ty
  name : String
  body : DSL.Stmt σ τ

/-- All callees reachable from a statement (callees of callees included), in call order. -/
def Stmt.callees : {Γ : List Ty} → {τ : Ty} → DSL.Stmt Γ τ → List Callee
  | _, _, .ret _ | _, _, .throw _ | _, _, .op _ => []
  | _, _, .call name body _ => ⟨_, _, name, body⟩ :: Stmt.callees body
  | _, _, .let_ _ k | _, _, .letPair _ k | _, _, .set _ _ k => Stmt.callees k
  | _, _, .vset _ _ _ k | _, _, .mapInsert _ _ _ k => Stmt.callees k
  | _, _, .bind s k => Stmt.callees s ++ Stmt.callees k
  | _, _, .ite _ t e => Stmt.callees t ++ Stmt.callees e
  | _, _, .forRange _ _ body => Stmt.callees body

/-- First occurrence of each name, excluding `seen`. -/
def dedupCallees (seen : List String) : List Callee → List Callee
  | [] => []
  | c :: cs =>
    if seen.contains c.name then dedupCallees seen cs
    else c :: dedupCallees (c.name :: seen) cs

/-- Compile a single DSL function (calls refer to the callees by mangled name). -/
def compileFn {σ : List Ty} {τ : Ty} (f : DSL.FlatFn σ τ) : Clif.Function :=
  compileBody f.name f.body

/-- Compile a DSL function and every function it transitively calls (each name once; the
entry function first). -/
def compile {σ : List Ty} {τ : Ty} (f : DSL.FlatFn σ τ) : Clif.Program :=
  { funcs := compileFn f ::
      (dedupCallees [f.name] (Stmt.callees f.body)).map fun c => compileBody c.name c.body }

end Compile
