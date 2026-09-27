import FV.Compile.Model
import FV.Compile.Runtime
import FV.DSL.TestCase

/-!
# Test harness: `; run:` lines and scalar test wrappers for emitted corpus files

A `; run:` line can only pass and compare scalars. A compiled function is called **directly**
when its ABI is scalar-only: no runtime context, no result buffer, no map in the parameters
or the result. Otherwise the emitter generates CLIF **test wrappers** `%<mangled>_w<j>`
(`docs/contracts/compile.md` §5):

* parameters: the *wire* encoding of the arguments: `flat`, except that each map is
  `len, k₀, v₀, …, k_{C-1}, v_{C-1}` (`i64` words, `C = capIn`, entries past `len` ignored);
* body: set up a 64 KiB map arena in a stack slot, build the map arguments with
  `flat_map_new`/`flat_map_insert`, call the function (with a result buffer in buffer mode),
  and on success serialise the result to its wire encoding (maps via `flat_map_len` and
  `flat_map_entry`, `C = capOut`, missing entries read as `0, 0`);
* result: `i8 tag` then chunk `j` (7 values) of the wire result, so that every wrapper fits the
  8 return registers; on error the chunk is zero.
-/

namespace Compile.Harness

open DSL (Ty)
open Clif (Val ValueId)

/-! ## Wire encoding -/

def wireTys (cap : Nat) : Ty → List Clif.Ty
  | .map _ _ => .i64 :: List.replicate (2 * cap) .i64
  | .vec n t => (List.replicate n (wireTys cap t)).flatten
  | .prod a b => wireTys cap a ++ wireTys cap b
  | t => flat t

def wireTysList (cap : Nat) : List Ty → List Clif.Ty
  | [] => []
  | t :: ts => wireTys cap t ++ wireTysList cap ts

def wireVal (cap : Nat) : (t : Ty) → t.denote → List Val
  | .int w, x => [.ofNat (intTy w) x.toNat]
  | .bool, b => [.ofBool b]
  | .unit, _ => []
  | .vec _ t, xs => xs.toList.flatMap (wireVal cap t)
  | .prod a b, (x, y) => wireVal cap a x ++ wireVal cap b y
  | .map k v, m =>
    let ws := m.entries.flatMap fun (a, b) => [toWord k a, toWord v b]
    .ofNat .i64 m.entries.length ::
      (ws ++ List.replicate (2 * cap - ws.length) 0#64).map fun x => .ofNat .i64 x.toNat

def wireArgs (cap : Nat) : (σ : List Ty) → DSL.Args σ → List Val
  | [], _ => []
  | t :: σ, (x, xs) => wireVal cap t x ++ wireArgs cap σ xs

/-- Sizes of all maps inside a value. -/
def mapSizes : (t : Ty) → t.denote → List Nat
  | .vec _ t, xs => xs.toList.flatMap (mapSizes t)
  | .prod a b, (x, y) => mapSizes a x ++ mapSizes b y
  | .map _ _, m => [m.entries.length]
  | _, _ => []

def argMapSizes : (σ : List Ty) → DSL.Args σ → List Nat
  | [], _ => []
  | t :: σ, (x, xs) => mapSizes t x ++ argMapSizes σ xs

/-- Is a test wrapper needed to call a function with this ABI from a run line? -/
def needsWrapper (abi : FnAbi) : Bool :=
  abi.ctx || abi.sret || abi.params.any Ty.hasMap || abi.result.hasMap

/-- Does the wrapper need a map arena? -/
def needsArena (abi : FnAbi) : Bool :=
  abi.ctx || abi.params.any Ty.hasMap || abi.result.hasMap

def arenaBytes : Nat := 65536

/-- Values per wrapper result chunk (plus the tag: 8 return registers). -/
def chunkSize : Nat := maxRegReturns - 1

def numChunks (n : Nat) : Nat := max 1 ((n + chunkSize - 1) / chunkSize)

def chunkOf {α : Type} (xs : List α) (j : Nat) : List α := (xs.drop (chunkSize * j)).take chunkSize

/-! ## Wrapper code -/

/-- Build one argument from its wire parameters; returns its flat values and the rest. -/
def buildArg (a : ValueId) (cap : Nat) : Ty → List ValueId → CGM (List ValueId × List ValueId)
  | .map _ _, ps => do
    let len := ps.headD 0
    let ws := ps.drop 1
    let h := (← callRt rtNew [a]).headD 0
    for e in List.range cap do
      let ev ← iconstN .i64 e
      let c ← inst1 (.icmp .ult .i64 ev len)
      let ins ← newBlock
      let nxt ← newBlock
      terminate (.brif c ⟨ins, []⟩ ⟨nxt, []⟩)
      switchTo ins []
      let _ ← callRt rtInsert [a, h, ws.getD (2 * e) 0, ws.getD (2 * e + 1) 0]
      terminate (.jump ⟨nxt, []⟩)
      switchTo nxt []
    pure ([h], ws.drop (2 * cap))
  | .vec n t, ps =>
    (List.range n).foldlM (init := ([], ps)) fun (acc, ps) _ => do
      let (xs, ps) ← buildArg a cap t ps
      pure (acc ++ xs, ps)
  | .prod x y, ps => do
    let (xs, ps) ← buildArg a cap x ps
    let (ys, ps) ← buildArg a cap y ps
    pure (xs ++ ys, ps)
  | t, ps => pure (ps.take (flat t).length, ps.drop (flat t).length)

/-- Serialise flat result values to the wire encoding; returns the wire values and the rest. -/
def serialize (a pk pv : ValueId) (cap : Nat) :
    Ty → List ValueId → CGM (List ValueId × List ValueId)
  | .map _ _, vs => do
    let h := vs.headD 0
    let len := (← callRt rtLen [a, h]).headD 0
    let es ← (List.range cap).mapM fun e => do
      let ev ← iconstN .i64 e
      let _ ← callRt rtEntry [a, h, ev, pk, pv]
      let k ← inst1 (.load .load .i64 slotFlags pk 0)
      let v ← inst1 (.load .load .i64 slotFlags pv 0)
      pure [k, v]
    pure (len :: es.flatten, vs.drop 1)
  | .vec n t, vs =>
    (List.range n).foldlM (init := ([], vs)) fun (acc, vs) _ => do
      let (xs, vs) ← serialize a pk pv cap t vs
      pure (acc ++ xs, vs)
  | .prod x y, vs => do
    let (xs, vs) ← serialize a pk pv cap x vs
    let (ys, vs) ← serialize a pk pv cap y vs
    pure (xs ++ ys, vs)
  | t, vs => pure (vs.take (flat t).length, vs.drop (flat t).length)

def wrapperName (callee : String) (j : Nat) : String := s!"{mangle callee}_w{j}"

/-- Test wrapper `j` for the compiled function `callee` with ABI `abi`. -/
def wrapper (abi : FnAbi) (callee : String) (capIn capOut j : Nat) : Clif.Function :=
  let wireIn := wireTysList capIn abi.params
  let outTys := chunkOf (wireTys capOut abi.result) j
  let gen : CGM Unit := do
    let ps ← freshFor wireIn
    switchTo 0 (ps.zip wireIn)
    let a ← if needsArena abi then do
        let s ← newSlot arenaBytes
        let a ← inst1 (.stackAddr .i64 s 0)
        let used ← iconstN .i64 16
        emitStmt [] (.store .store .i64 slotFlags used a 0)
        let cap ← iconstN .i64 arenaBytes
        emitStmt [] (.store .store .i64 slotFlags cap a 8)
        pure (some a)
      else pure none
    let (args, _) ← abi.params.foldlM (init := ([], ps)) fun (acc, ps) t => do
      let (xs, ps) ← buildArg (a.getD 0) capIn t ps
      pure (acc ++ xs, ps)
    let buf ← if abi.sret then do
        let s ← newSlot abi.bufSize
        pure (some (← inst1 (.stackAddr .i64 s 0)))
      else pure none
    let ctxArg := if abi.ctx then [a.getD 0] else []
    let res ← callFn (mangle callee) abi.signature (ctxArg ++ buf.toList ++ args)
    let tag := res.headD 0
    let ok ← newBlock
    let bad ← newBlock
    terminate (.brif tag ⟨bad, []⟩ ⟨ok, []⟩)
    switchTo bad []
    let zs ← outTys.mapM fun ty => iconstN ty 0
    terminate (.ret (tag :: zs))
    switchTo ok []
    let payload ← match buf with
      | some p => loadVals p (flat abi.result)
      | none => pure res.tail
    let wire ← if needsArena abi then do
        let s ← newSlot 16
        let pk ← inst1 (.stackAddr .i64 s 0)
        let pv ← inst1 (.stackAddr .i64 s 8)
        pure (← serialize (a.getD 0) pk pv capOut abi.result payload).1
      else pure payload
    terminate (.ret (tag :: chunkOf wire j))
  let s := (gen.run {}).2
  { name := wrapperName callee j
    sig := { params := wireIn.map fun t => { ty := t }
             returns := (Clif.Ty.i8 :: outTys).map fun t => { ty := t } }
    slots := s.slots
    externs := s.externs
    blocks := s.done.reverse }

/-! ## Emitted test files -/

/-- Encoding of a result for a run line: tag, then the (wire) payload `vals` or zeros. -/
def expectVals {t : Ty} (payloadTys : List Clif.Ty) (enc : t.denote → List Val) :
    DSL.M t.denote → List Val
  | .ok x => .ofNat .i8 0 :: enc x
  | .error e => .ofNat .i8 e.tag :: payloadTys.map fun ty => .ofNat ty 0

/-- Flat argument values of a map-free argument tuple. -/
def directArgs (σ : List Ty) (args : DSL.Args σ) : List Val := wireArgs 0 σ args

def header : List String := ["test interpret", "test run", "target aarch64"]

/-- Does the program call the map runtime? -/
def usesRuntime (fs : List Clif.Function) : Bool :=
  fs.any fun f => f.externs.any fun (_, e) => Runtime.names.contains e.name

/-- The test program of a corpus case: the compiled program, run lines (on the function or on
its wrappers) with expectations `denote` encoded per the ABI, and, if `withRuntime` and the
program calls the runtime, the CLIF map runtime. -/
def testProgram (tc : DSL.TestCase) (withRuntime : Bool := true) : Except String Clif.Program := do
  let p := compile tc.fn
  let abi := fnAbi tc.fn
  let results := tc.vectors.map fun v => DSL.denote tc.fn v.args
  let funcs ←
    if needsWrapper abi then do
      let capIn := (tc.vectors.flatMap fun v => argMapSizes tc.σ v.args).foldl max 0
      let capOut := (results.flatMap fun
        | .ok x => mapSizes tc.τ x
        | .error _ => []).foldl max 0
      let outTys := wireTys capOut tc.τ
      let wrappers := (List.range (numChunks outTys.length)).map fun j =>
        let w := wrapper abi tc.fn.name capIn capOut j
        let runs := (tc.vectors.zip results).map fun (v, r) =>
          { func := w.name, args := wireArgs capIn tc.σ v.args
            expect := .eq (expectVals (chunkOf outTys j)
              (fun x => chunkOf (wireVal capOut tc.τ x) j) r) : Clif.RunCommand }
        { w with runs }
      pure (p.funcs ++ wrappers)
    else
      let runs := (tc.vectors.zip results).map fun (v, r) =>
        { func := mangle tc.fn.name, args := directArgs tc.σ v.args
          expect := .eq (expectVals (flat tc.τ) (wireVal 0 tc.τ) r) : Clif.RunCommand }
      match p.funcs with
      | f :: fs => pure ({ f with runs } :: fs)
      | [] => throw "empty program"
  let rt ← if withRuntime && usesRuntime funcs then Runtime.functions else pure []
  pure { header, funcs := funcs ++ rt }

end Compile.Harness
