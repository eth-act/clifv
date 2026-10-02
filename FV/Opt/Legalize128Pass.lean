import FV.Opt.Legal

/-!
# `Opt.Legalize128`: the pass

The rewrite itself (the type map, the ABI groups and the certificate type are in
`FV/Opt/Legalize128.lean`, the validator and the canonical patterns in `FV/Opt/Legal.lean`).
The pass is driven by the validator's plans: it first gives every `i128` value of `f` a pair of
fresh `i64` values (`allocPairs`, the certificate), then rewrites each statement by its
`Opt.Legal.planOf` plan, emitting the plan's canonical pattern with fresh temporaries
(`emitPat`). A statement without a plan makes the legalisation fail (the function is left alone
and reported unsupported by the backend). `Opt.Legal.check` validates the result; it accepts
every legalisation of a function satisfying `Opt.Legal.Complete.Pre`
(`Opt.Legal.Complete.check_complete`, `FV/Opt/Proof/LegalComplete.lean`).
-/

namespace Opt.Legalize128

open Clif Opt.Legal

/-! ## The certificate -/

/-- The pair of every `i128` value of `f` (a definition of type `i128`): consecutive ids from
`n`. -/
def allocPairs (f : Function) (n : ValueId) : List (ValueId × ValueId × ValueId) :=
  (((defsOf f).filter (·.2.1 == some .i128)).map (·.1)).zipIdx.map fun (v, i) =>
    (v, n + 2 * i, n + 2 * i + 1)

/-! ## The legaliser's state -/

structure St where
  next : ValueId
  /-- Statements emitted for the block being rewritten (in order). -/
  out : List Stmt := []

abbrev M := StateT St (Except String)

def fresh : M ValueId := do
  let st ← get
  set { st with next := st.next + 1 }
  return st.next

def emitS (st' : Stmt) : M Unit :=
  modify fun s => { s with out := s.out ++ [st'] }

def emitN (l : List Stmt) : M Unit :=
  modify fun s => { s with out := s.out ++ l }

def liftE {α : Type} (r : Except String α) : M α :=
  match r with
  | .ok a => pure a
  | .error e => throw e

def pairOf (C : Ctx) (v : ValueId) : M (ValueId × ValueId) :=
  match C.pair v with
  | some p => pure p
  | none => throw s!"legalize128: v{v} is not an i128 value"

/-! ## Patterns -/

/-- The renaming of a pattern instance: inputs, outputs, and the temporary `c` as `base + c`. -/
def patRen (ins outs : List ValueId) (base c : ValueId) : ValueId :=
  if h : c < ins.length then ins[c]
  else if h2 : c - ins.length < outs.length then outs[c - ins.length]
  else base + c

/-- The ids a pattern instance reserves for its temporaries. -/
def patSpan (pat : List Stmt) : Nat := (written pat).foldl max 0 + 1

/-- Emit an instance of a canonical pattern. -/
def emitPat (pat : List Stmt) (ins outs : List ValueId) : M Unit :=
  modify fun s => { s with next := s.next + patSpan pat,
                           out := s.out ++ pat.map (renameStmt (patRen ins outs s.next)) }

/-! ## Calls -/

/-- The `__*ti3` helpers `f`'s `i128` divisions call, declared after `f`'s externs. -/
def helperNames (f : Function) : List String :=
  (f.blocks.flatMap fun b => b.body.filterMap fun s => match s.inst with
    | .div op .i128 _ _ => some (divHelper op)
    | _ => none).eraseDups

def helperExts (f : Function) : List (FnRef × ExtFunc) :=
  (helperNames f).zipIdx.map fun (n, i) => (maxFnRef f + 1 + i, { name := n, sig := helperSig })

/-- The results of an expanded call (`retsOk`): pads are fresh. -/
def retsOf (C : Ctx) : List (List SlotEl) → List ValueId → M (List ValueId)
  | [], [] => pure []
  | [.val _] :: gs, r :: rs =>
    if C.plain r then do return r :: (← retsOf C gs rs)
    else throw s!"legalize128: v{r} is an i128 value"
  | [.lo, .hi] :: gs, r :: rs => do
    let (a, b) ← pairOf C r
    return a :: b :: (← retsOf C gs rs)
  | [.pad, .lo, .hi] :: gs, r :: rs => do
    let w ← fresh
    let (a, b) ← pairOf C r
    return w :: a :: b :: (← retsOf C gs rs)
  | _, _ => throw "legalize128: return slots do not match the signature"

def expandExterns : List (FnRef × ExtFunc) → Except String (List (FnRef × ExtFunc))
  | [] => pure []
  | (r, e) :: es => do
    let s ← expandSig e.sig
    return (r, { e with sig := s }) :: (← expandExterns es)

def expandSigDecls : List (Nat × Signature) → Except String (List (Nat × Signature))
  | [] => pure []
  | (i, s) :: ds => do
    let s' ← expandSig s
    return (i, s') :: (← expandSigDecls ds)

/-! ## Statements -/

/-- Emit the segment of a plan. -/
def emitPlan (C : Ctx) (s : Stmt) : Plan → M Unit
  | .same | .callInd => emitS s
  | .pure pat ins outs => emitPat pat ins outs
  | .load rl rh p fl off =>
    emitN [S rl (.load .load .i64 fl p off), S rh (.load .load .i64 fl p (off + 8))]
  | .store xl xh p fl off =>
    emitN [{ results := [], inst := .store .store .i64 fl xl p off },
           { results := [], inst := .store .store .i64 fl xh p (off + 8) }]
  | .div op xl xh yl yh rl rh =>
    match (helperExts C.f).find? (·.2 == helperExt op) with
    | some (fn, _) => emitS { results := [rl, rh], inst := .call fn [xl, xh, yl, yh] }
    | none => throw "legalize128: no helper declaration"
  | .call fn _ args rg rs => do
    let results ← retsOf C rg rs
    emitS { results, inst := .call fn args }
  | .trap lo hi nz code => do
    let c ← fresh
    emitPat Pat.cond [lo, hi] [c]
    emitS { results := [], inst := if nz then .trapnz c code else .trapz c code }

/-- A statement by its plan. -/
def emitStmt (C : Ctx) (s : Stmt) : M Unit :=
  match planOf C s with
  | some pl => emitPlan C s pl
  | none => throw "legalize128: unsupported statement"

/-- The rewrite of one statement. A `call_indirect` with an `i128` signature is expanded by the
ABI groups (outside `Opt.Legal.check`: such functions are flagged unverified). -/
def rewriteStmt (C : Ctx) (s : Stmt) : M Unit :=
  match s.inst with
  | .callIndirect sig callee args =>
    match C.f.sigDecls.lookup sig with
    | some d =>
      if sig128 d then do
        let gs ← liftE (expandGroups d.params)
        let rg ← liftE (expandGroups d.returns)
        let some args' := expandArgs C gs args | throw "legalize128: call_indirect arguments"
        let results ← retsOf C rg s.results
        emitS { results, inst := .callIndirect sig callee args' }
      else emitStmt C s
    | none => throw s!"legalize128: unknown sig{sig}"
  | _ => emitStmt C s

def rewriteBody (C : Ctx) : List Stmt → M Unit
  | [] => pure ()
  | s :: ss => do
    rewriteStmt C s
    rewriteBody C ss

/-! ## Block parameters and terminators -/

/-- The parameters of the entry block (`entryParamsOk`): pads are fresh. -/
def entryParams (C : Ctx) : List (List SlotEl) → List (ValueId × Ty) → M (List (ValueId × Ty))
  | [], [] => pure []
  | [.val p] :: gs, (v, t) :: ps =>
    if t == p.ty && C.plain v then do return (v, t) :: (← entryParams C gs ps)
    else throw "legalize128: entry parameter does not match the signature"
  | [.lo, .hi] :: gs, (v, t) :: ps =>
    if t == .i128 then do
      let (a, b) ← pairOf C v
      return (a, .i64) :: (b, .i64) :: (← entryParams C gs ps)
    else throw "legalize128: entry parameter does not match the signature"
  | [.pad, .lo, .hi] :: gs, (v, t) :: ps =>
    if t == .i128 then do
      let w ← fresh
      let (a, b) ← pairOf C v
      return (w, .i64) :: (a, .i64) :: (b, .i64) :: (← entryParams C gs ps)
    else throw "legalize128: entry parameter does not match the signature"
  | _, _ => throw "legalize128: parameter slots do not match the signature"

/-- The parameters of a non-entry block (`paramsOk`). -/
def blockParams (C : Ctx) : List (ValueId × Ty) → M (List (ValueId × Ty))
  | [] => pure []
  | (v, t) :: ps =>
    if t == .i128 then do
      let (a, b) ← pairOf C v
      return (a, .i64) :: (b, .i64) :: (← blockParams C ps)
    else if C.plain v then do return (v, t) :: (← blockParams C ps)
    else throw s!"legalize128: v{v} is an i128 value"

/-- A branch (`bcOk`). -/
def rewriteBC (C : Ctx) (bc : BlockCall) : M BlockCall :=
  if C.entryId? == some bc.block then throw "legalize128: branch to the entry block"
  else match C.f.block? bc.block with
    | some B =>
      match expandBC C bc.args B.params with
      | some args => pure { bc with args }
      | none => throw s!"legalize128: arguments of block{bc.block}"
    | none => throw s!"legalize128: unknown block{bc.block}"

/-- A `try_call` successor (exception handlers, `try_call_indirect`): an `i128` value is split
into its pair; `retN` of an `i128` return becomes the two return slots of its pair (after a
pad); payloads (`exnN`, pointer-sized) are unchanged. -/
def rewriteTryDest (C : Ctx) (rg : List (List SlotEl)) (d : TryDest) :
    Except String TryDest := do
  let some tb := C.f.block? d.block | throw s!"legalize128: unknown block{d.block}"
  let starts := (rg.foldl (fun (acc, n) g => (acc.push n, n + g.length)) (#[], 0)).1
  let pairOf (v : ValueId) : Except String (ValueId × ValueId) :=
    match C.pair v with
    | some p => pure p
    | none => throw s!"legalize128: v{v} is not an i128 value"
  let rec go : List TryArg → List (ValueId × Ty) → Except String (List TryArg)
    | [], [] => return []
    | a :: as, (_, t) :: ps => do
      let more ← go as ps
      match a with
      | .val v =>
        if t == .i128 then do
          let (x, y) ← pairOf v
          return .val x :: .val y :: more
        else return .val v :: more
      | .ret i =>
        match rg[i]?, starts[i]? with
        | some [.val _], some s => return .ret s :: more
        | some [.lo, .hi], some s => return .ret s :: .ret (s + 1) :: more
        | some [.pad, .lo, .hi], some s => return .ret (s + 1) :: .ret (s + 2) :: more
        | _, _ => throw s!"legalize128: try_call ret{i}"
      | .exn i => return .exn i :: more
    | _, _ => throw s!"legalize128: arity of block{d.block}"
  return { d with args := ← go d.args tb.params }

def rewriteItems (C : Ctx) (rg : List (List SlotEl)) (items : List ExnItem) :
    Except String (List ExnItem) :=
  items.mapM fun
    | .tag n d => do return ExnItem.tag n (← rewriteTryDest C rg d)
    | .default d => do return ExnItem.default (← rewriteTryDest C rg d)
    | .context v => do return ExnItem.context v

/-- The rewrite of a terminator (`termOk`; its condition statements are emitted into `out`).
`try_call_indirect` is expanded outside `Opt.Legal.check`. -/
def rewriteTerm (C : Ctx) (rg : List (List SlotEl)) : Terminator → M Terminator
  | .jump bc => return .jump (← rewriteBC C bc)
  | .brif c t e => do
    let c' ← match C.pair c with
      | some (lo, hi) => do
        let c' ← fresh
        emitPat Pat.cond [lo, hi] [c']
        pure c'
      | none => pure c
    return .brif c' (← rewriteBC C t) (← rewriteBC C e)
  | .brTable x d tbl =>
    if C.plain x then return .brTable x (← rewriteBC C d) (← tbl.mapM (rewriteBC C))
    else throw "legalize128: i128 br_table index"
  | .ret vs =>
    match expandArgs C rg vs with
    | some vs' => pure (.ret vs')
    | none => throw "legalize128: return values do not match the signature"
  | .trap c => pure (.trap c)
  | .returnCall .. => throw "legalize128: return_call is not supported"
  | .tryCall fn args et => do
    let some e := C.f.extern? fn | throw s!"legalize128: unknown fn{fn}"
    let some d' := C.g.sigDecls.lookup et.sig | throw s!"legalize128: unknown sig{et.sig}"
    let s' ← liftE (expandSig e.sig)
    let gs ← liftE (expandGroups e.sig.params)
    let rgs ← liftE (expandGroups e.sig.returns)
    if !(AbiParam.tys d'.params == AbiParam.tys s'.params &&
        AbiParam.tys d'.returns == AbiParam.tys s'.returns) then
      throw s!"legalize128: sig{et.sig} is not the signature of fn{fn}"
    if C.entryId? == some et.normal.block then throw "legalize128: branch to the entry block"
    if !decide (C.T0 ≤ C.f.freshValue) then throw "legalize128: try_call without values"
    let some B := C.f.block? et.normal.block | throw s!"legalize128: unknown block{et.normal.block}"
    let some args' := expandArgs C gs args | throw "legalize128: try_call arguments"
    let some nargs := expandTry C rgs et.normal.args B.params
      | throw "legalize128: try_call normal-return arguments"
    let items ← liftE (rewriteItems C rgs et.items)
    return .tryCall fn args' { et with normal := { et.normal with args := nargs }, items }
  | .tryCallIndirect c args et => do
    let some sig := C.f.sigDecls.lookup et.sig | throw s!"legalize128: unknown sig{et.sig}"
    let gs ← liftE (expandGroups sig.params)
    let rgs ← liftE (expandGroups sig.returns)
    let some args' := expandArgs C gs args | throw "legalize128: try_call arguments"
    let normal ← liftE (rewriteTryDest C rgs et.normal)
    let items ← liftE (rewriteItems C rgs et.items)
    return .tryCallIndirect c args' { et with normal, items }

/-! ## Blocks and the function -/

def rewriteBlock (C : Ctx) (pg rg : List (List SlotEl)) (isEntry : Bool) (b : Block) :
    M Block := do
  modify fun s => { s with out := [] }
  let params ← if isEntry then entryParams C pg b.params else blockParams C b.params
  if isEntry then emitS C.zeroStmt
  rewriteBody C b.body
  let term ← rewriteTerm C rg b.term
  let st ← get
  return { b with params, body := st.out, term }

def rewriteBlocks (C : Ctx) (pg rg : List (List SlotEl)) : Bool → List Block → M (List Block)
  | _, [] => pure []
  | isEntry, b :: bs => do
    let b' ← rewriteBlock C pg rg isEntry b
    return b' :: (← rewriteBlocks C pg rg false bs)

/-- The legalised function and its certificate (an error makes the caller keep the
original, which the backend then reports unsupported as before). -/
def function128Cert (f : Function) : Except String (Function × Cert) := do
  if !(mentions128 f) then return (f, {})
  if f.blocks.isEmpty then throw "legalize128: no blocks"
  let n0 := maxValueId f + 1
  let pairs := allocPairs f n0
  let cert : Cert := { pairs, zero := n0 + 2 * pairs.length }
  let sig ← expandSig f.sig
  let externs ← expandExterns f.externs
  let sigDecls ← expandSigDecls f.sigDecls
  let g0 : Function := { f with sig, externs := externs ++ helperExts f, sigDecls }
  let pg ← expandGroups f.sig.params
  let rg ← expandGroups f.sig.returns
  let (blocks, _) ← (rewriteBlocks ⟨f, g0, cert⟩ pg rg true f.blocks).run { next := cert.zero + 1 }
  return ({ g0 with blocks }, cert)

/-- The legalised function. -/
def function128 (f : Function) : Except String Function :=
  (·.1) <$> function128Cert f

namespace Opt.Legalize128

/-- The unverified reason of a legalised function the validator rejects. -/
def rejectedReason : String := "i128 legalized (outside backend_correct: Opt.Legal.check rejects)"

/-- The unverified reason of an accepted legalised function that declares an extern named
like a function of the file (`E2E.backend_correct_legal`'s `hext`/`hext'`: calls go to the
environment). -/
def externClashReason : String :=
  "i128 legalized (outside backend_correct_legal: an extern is named like a function of the file)"

/-- The unverified reason of an accepted legalised function with a `call_indirect` when the
legalised file's externs do not extend the original file's (`E2E.backend_correct_legal`'s
`hind`: an indirect call resolves to the same extern in both programs). -/
def indExternsReason : String :=
  "i128 legalized (outside backend_correct_legal: call_indirect, and the legalised file's externs do not extend the original's)"

/-- Does `f` have a `call_indirect`? -/
def hasCallInd (f : Clif.Function) : Bool :=
  f.blocks.any fun b => b.body.any fun st => match st.inst with
    | .callIndirect .. => true
    | _ => false

/-- The names of the externs the parsed functions of a file declare (`Clif.Program.externNames`
of the file's program). -/
def externNamesOf (pf : Clif.ParsedFile) : List String :=
  (pf.funcs.filterMap (·.func.toOption)).flatMap fun f => f.externs.map (·.2.name)

/-- The result of `parsedFile128`. -/
structure Legalized where
  /-- The file with every legalisable function replaced by its legalisation. -/
  file : Clif.ParsedFile
  /-- The legalised functions outside `E2E.backend_correct_legal`, with the reason. -/
  unverified : List (String × String)
  /-- The legalised functions `Opt.Legal.check` accepts (without extern-name clash): inside
  `E2E.backend_correct_legal` whenever the backend's own conditions (`InSubset` of the
  legalised function, `lowerCheck`) hold, which `Backend.compileFileWith` decides. -/
  accepted : List String

/-- Legalise every parsed function of a file. A legalised function the validator
`Opt.Legal.check` accepts, whose externs are not named like functions of the file, is covered
by `E2E.backend_correct_legal` (the backend decides the remaining conditions on the
legalised function like on any other); the others are flagged unverified. -/
def parsedFile128 (pf : Clif.ParsedFile) : Legalized :=
  let own := pf.funcs.map (·.name)
  let clash (f : Clif.Function) : Bool := f.externs.any fun e => own.contains e.2.name
  let lg := parsedFile128Fold pf own clash
  -- `hind`: with an indirect call, the legalised file's externs must extend the original's
  if (externNamesOf pf).isPrefixOf (externNamesOf lg.file) then lg
  else
    let ind := lg.accepted.filter fun n =>
      pf.funcs.any fun p => p.name == n && match p.func with
        | .ok f => hasCallInd f
        | .error _ => false
    { lg with accepted := lg.accepted.filter (!ind.contains ·),
              unverified := lg.unverified ++ ind.map (·, indExternsReason) }
where
  parsedFile128Fold (pf : Clif.ParsedFile) (own : List String) (clash : Clif.Function → Bool) :
      Legalized :=
  pf.funcs.foldl (fun (acc : Legalized) p =>
    let push (f : Clif.ParsedFunction) : Clif.ParsedFile :=
      { acc.file with funcs := acc.file.funcs ++ [f] }
    match p.func with
    | .ok f =>
      match function128Cert f with
      | .ok (f', cert) =>
        if f' == f then { acc with file := push p }
        else
          let acc := { acc with file := push { p with func := .ok f' } }
          if !Opt.Legal.check f f' cert then
            { acc with unverified := acc.unverified ++ [(p.name, rejectedReason)] }
          else if clash f || clash f' then
            { acc with unverified := acc.unverified ++ [(p.name, externClashReason)] }
          else { acc with accepted := acc.accepted ++ [p.name] }
      | .error _ => { acc with file := push p }
    | .error _ => { acc with file := push p }) ⟨{ pf with funcs := [] }, [], []⟩

end Opt.Legalize128
