import FV.Compile.Emit

/-!
# Lean model of the map runtime, argument encoding, result decoding

`Compile.mapEnv : Clif.Env` gives the map externs (`docs/contracts/compile.md` §4) their
meaning directly in terms of `DSL.Map`'s operations on entry lists (`lookupL`, `upsertL`), so
the dsl.md laws hold by construction. Map objects live in `Clif.Mem`:

* a map handle `h` is the address of a 16-byte header: `len : u64` at `h`, `data : u64` at `h+8`;
* `data` points to `len` entries of 16 bytes: key word at `+0`, value word at `+8` (words are
  keys/values zero-extended to 64 bits, `Compile.toWord`).

Every insert writes a fresh entry array (`Mem.alloc`); handles are stable. The context
argument is ignored (the model allocates with `Mem.alloc`).

`setupCall`/`decodeResult`/`runCompiled` are the harness the M2 theorem is stated with.
-/

namespace Compile

open DSL (Ty IntW)
open Clif (Val Mem Outcome Res)

/-- Continue with the value of a `Res`, as an `Outcome`. -/
def Res.toOutcome {α : Type} (r : Res α) (k : α → Outcome) : Outcome :=
  match r with
  | .ok a => k a
  | .trap c => .trapped c
  | .stuck m => .stuck m

/-- Entry arrays longer than this are treated as corrupt (guards the model against garbage). -/
def maxEntries : Nat := 1 <<< 20

def readWord (m : Mem) (addr : Nat) : Res (BitVec 64) := m.load {} addr 8 64

def writeWord (m : Mem) (addr : Nat) (x : BitVec 64) : Res Mem := m.store {} addr 8 x

/-- The entry list of the map object at `h`. -/
def readEntries (m : Mem) (h : Nat) : Res (List (BitVec 64 × BitVec 64)) := do
  let len ← readWord m h
  let data ← readWord m (h + 8)
  Res.check (len.toNat ≤ maxEntries) s!"map at {h}: corrupt length {len.toNat}"
  (List.range len.toNat).mapM fun i => do
    let k ← readWord m (data.toNat + 16 * i)
    let v ← readWord m (data.toNat + 16 * i + 8)
    pure (k, v)

/-- Replace the entries of the map object at `h` by `es` (fresh entry array). -/
def writeEntries (m : Mem) (h : Nat) (es : List (BitVec 64 × BitVec 64)) : Res Mem := do
  let (data, m) := m.alloc (16 * es.length) 16
  let m ← (es.zip (List.range es.length)).foldlM (init := m) fun m ((k, v), i) => do
    let m ← writeWord m (data + 16 * i) k
    writeWord m (data + 16 * i + 8) v
  let m ← writeWord m h (BitVec.ofNat 64 es.length)
  writeWord m (h + 8) (BitVec.ofNat 64 data)

/-- A new map object with entries `es`; returns its handle. -/
def newMapObj (m : Mem) (es : List (BitVec 64 × BitVec 64)) : Res (Nat × Mem) := do
  let (h, m) := m.alloc 16 16
  let m ← writeEntries m h es
  pure (h, m)

def ret1 (v : Val) (m : Mem) : Outcome := .returned [v] m

/-- The extern semantics of the map runtime (arguments are type-checked by `Clif.run` against
the declarations, `Compile.rtNew` …). -/
def mapExtern : String → Option (List Val → Mem → Outcome)
  | "flat_map_new" => some fun
    | [_], m => Res.toOutcome (newMapObj m []) fun (h, m) => ret1 (.ofNat .i64 h) m
    | _, _ => .stuck "flat_map_new: arity"
  | "flat_map_insert" => some fun
    | [_, h, k, v], m => Res.toOutcome (readEntries m h.toNat) fun es =>
      Res.toOutcome (writeEntries m h.toNat
          (DSL.Map.upsertL (BitVec.ofNat 64 k.toNat) (BitVec.ofNat 64 v.toNat) es)) fun m =>
        .returned [] m
    | _, _ => .stuck "flat_map_insert: arity"
  | "flat_map_contains" => some fun
    | [_, h, k], m => Res.toOutcome (readEntries m h.toNat) fun es =>
      ret1 (.ofBool (DSL.Map.lookupL (BitVec.ofNat 64 k.toNat) es).isSome) m
    | _, _ => .stuck "flat_map_contains: arity"
  | "flat_map_get" => some fun
    | [_, h, k, out], m => Res.toOutcome (readEntries m h.toNat) fun es =>
      match DSL.Map.lookupL (BitVec.ofNat 64 k.toNat) es with
      | some v => Res.toOutcome (writeWord m out.toNat v) fun m => ret1 (.ofBool true) m
      | none => ret1 (.ofBool false) m
    | _, _ => .stuck "flat_map_get: arity"
  | "flat_map_clone" => some fun
    | [_, h], m => Res.toOutcome (readEntries m h.toNat) fun es =>
      Res.toOutcome (newMapObj m es) fun (h', m) => ret1 (.ofNat .i64 h') m
    | _, _ => .stuck "flat_map_clone: arity"
  | "flat_map_len" => some fun
    | [_, h], m => Res.toOutcome (readEntries m h.toNat) fun es =>
      ret1 (.ofNat .i64 es.length) m
    | _, _ => .stuck "flat_map_len: arity"
  | "flat_map_entry" => some fun
    | [_, h, i, kp, vp], m => Res.toOutcome (readEntries m h.toNat) fun es =>
      let (k, v) := es[i.toNat]?.getD (0#64, 0#64)
      Res.toOutcome (writeWord m kp.toNat k) fun m =>
      Res.toOutcome (writeWord m vp.toNat v) fun m => .returned [] m
    | _, _ => .stuck "flat_map_entry: arity"
  | _ => none

def mapEnv : Clif.Env := { extern := mapExtern }

/-! ## Encoding DSL values -/

/-- Encode a value as its flattened CLIF values; maps are created in memory. -/
def encodeVal : (t : Ty) → t.denote → Mem → Res (List Val × Mem)
  | .int w, x, m => pure ([.ofNat (intTy w) x.toNat], m)
  | .bool, b, m => pure ([.ofBool b], m)
  | .unit, _, m => pure ([], m)
  | .vec _ t, xs, m =>
    xs.toList.foldlM (init := ([], m)) fun (acc, m) x => do
      let (vs, m) ← encodeVal t x m
      pure (acc ++ vs, m)
  | .prod a b, (x, y), m => do
    let (vs, m) ← encodeVal a x m
    let (ws, m) ← encodeVal b y m
    pure (vs ++ ws, m)
  | .map k v, mp, m => do
    let (h, m) ← newMapObj m (mp.entries.map fun (a, b) => (toWord k a, toWord v b))
    pure ([.ofNat .i64 h], m)

def encodeArgs : (σ : List Ty) → DSL.Args σ → Mem → Res (List Val × Mem)
  | [], _, m => pure ([], m)
  | t :: σ, (x, xs), m => do
    let (vs, m) ← encodeVal t x m
    let (ws, m) ← encodeArgs σ xs m
    pure (vs ++ ws, m)

/-! ## Decoding DSL values -/

/-- Decode a value from the front of `vs` (maps read from `m`); `none` if the values are not
a canonical encoding. Returns the remaining values. -/
def decodeVal : (t : Ty) → List Val → Mem → Option (t.denote × List Val)
  | .int w, v :: vs, _ =>
    if v.ty = intTy w then some (BitVec.ofNat w.bits v.toNat, vs) else none
  | .bool, v :: vs, _ =>
    if v.ty = .i8 ∧ v.toNat ≤ 1 then some (v.toNat = 1, vs) else none
  | .unit, vs, _ => some ((), vs)
  | .vec n t, vs, m => do
    let (xs, vs) ← (List.range n).foldlM (init := (([] : List t.denote), vs)) fun (acc, vs) _ => do
      let (x, vs) ← decodeVal t vs m
      pure (acc ++ [x], vs)
    if h : xs.length = n then some (⟨xs.toArray, by simp [h]⟩, vs) else none
  | .prod a b, vs, m => do
    let (x, vs) ← decodeVal a vs m
    let (y, vs) ← decodeVal b vs m
    some ((x, y), vs)
  | .map k v, hv :: vs, m => do
    guard (hv.ty = .i64)
    let es ← match readEntries m hv.toNat with
      | .ok es => some es
      | _ => none
    let es ← es.mapM fun (a, b) => do pure (← ofWord? k a, ← ofWord? v b)
    some (⟨es⟩, vs)
  | _, [], _ => none

/-! ## Calling a compiled function -/

/-- Arguments and initial memory for calling a compiled function. -/
structure CallSetup where
  args : List Val
  mem : Mem
  /-- address of the result buffer (buffer mode) -/
  buf : Option Nat

/-- Encode `args` for `abi`: context `0` (ignored by `mapEnv`), a fresh result buffer in buffer
mode, then the flattened arguments. -/
def setupCall (abi : FnAbi) (args : DSL.Args abi.params) : Res CallSetup := do
  let (vs, m) ← encodeArgs abi.params args Mem.empty
  let (buf, m) := if abi.sret then
      let (b, m) := m.alloc abi.bufSize 16
      (some b, m)
    else (none, m)
  pure { args := (if abi.ctx then [Val.ofNat .i64 0] else []) ++
                 (buf.map fun b => Val.ofNat .i64 b).toList ++ vs
         mem := m, buf }

/-- Read `tys` from a result buffer (8 bytes per value). -/
def readBuf (m : Mem) (buf : Nat) (tys : List Clif.Ty) : Option (List Val) :=
  (tys.zip (List.range tys.length)).mapM fun (ty, j) =>
    match m.load {} (buf + 8 * j) ty.bytes ty.width with
    | .ok x => some ⟨ty, x⟩
    | _ => none

/-- Decode a finished run per the error-tag ABI: tag `0` with the decoded payload, or
`Err.ofTag tag` with an all-zero payload. `none` for anything else (trap, stuck, out of fuel,
ill-typed or non-canonical results). -/
def decodeResult (abi : FnAbi) (buf : Option Nat) : Outcome → Option (DSL.M abi.result.denote)
  | .returned (tag :: rest) m => do
    guard (tag.ty = .i8)
    let payload ← match buf with
      | some b => do guard rest.isEmpty; readBuf m b (flat abi.result)
      | none => some rest
    if tag.toNat = 0 then
      let (x, left) ← decodeVal abi.result payload m
      guard left.isEmpty
      some (.ok x)
    else
      guard (payload.all (·.toNat == 0) && payload.length == (flat abi.result).length)
      let e ← DSL.Err.ofTag tag.toNat
      some (.error e)
  | _ => none

/-- Fuel for running compiled corpus functions. -/
def defaultFuel : Nat := 10000000

/-- Run the compiled program of `f` on `args` through `Clif.run` with the map model. -/
def runCompiled {σ : List Ty} {τ : Ty} (f : DSL.FlatFn σ τ) (args : DSL.Args σ)
    (fuel : Nat := defaultFuel) : Option (DSL.M τ.denote) :=
  let abi : FnAbi := fnAbi f
  match setupCall abi args with
  | .ok s => decodeResult abi s.buf
      (Clif.runWith mapEnv (compile f) (mangle f.name) s.args s.mem fuel)
  | _ => none

end Compile
