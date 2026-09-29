import FV.Clif.Syntax

/-!
# CLIF text parser (subset S)

`Clif.parse : String → Except String Program` parses a whole `.clif` file whose functions
are all in subset S. `Clif.parseFile` is the per-function version used by the filetest
runner: functions outside S are reported as `ParseError.unsupported` with a reason, the
others are parsed normally.

Accepted input (Cranelift 0.136.1 reader syntax):
* header lines `test ...`, `target ...`, `set ...` before the first function (kept verbatim),
  and `; data:` directives there (link-time data objects, see `dataDirective`);
* `function %name(params) [-> returns] [callconv] { preamble blocks }`;
* preamble: `ssN = explicit_slot N[, align = K]`, `gvN = vmctx | load.ty flags gvM[+off] |
  iadd_imm.ty gvM, off | symbol [colocated] %name[+off]`, `fnN = [colocated] %name(sig)`;
* blocks `blockN[(vA: ty, ...)] [cold]:`, value aliases `vA -> vB` (resolved away), and the
  instructions of S with optional `.ty` suffixes (inferred from the typevar operand when
  omitted);
* comments after `function` (inside or after the body, up to the next function) of the
  forms `; run: %f(args) == expected`, `; run: %f(args) != expected`, bare `; run` and
  `; print: %f(args)`, where values are decimal, negative, or hex with `_` separators.
  Arguments and expectations are typed by the signature of the function the comment is
  attached to (as in the reader).
-/

namespace Clif

/-- Parse errors. `unsupported`: valid CLIF outside subset S (opcode, type or feature);
`malformed`: anything else. -/
inductive ParseError where
  | unsupported (msg : String)
  | malformed (msg : String)
  deriving Repr, Inhabited, BEq

def ParseError.toString : ParseError → String
  | .unsupported m => s!"unsupported: {m}"
  | .malformed m => s!"parse error: {m}"

instance : ToString ParseError := ⟨ParseError.toString⟩

namespace Parse

/-! ## Lexer -/

inductive Tok where
  | word (s : String)
  /-- `%name` (without the `%`). -/
  | name (s : String)
  /-- Integer literal text, including a leading sign if present. -/
  | int (s : String)
  | arrow
  | punct (c : Char)
  deriving Repr, BEq, Inhabited

def Tok.show : Tok → String
  | .word s => s | .name s => "%" ++ s | .int s => s | .arrow => "->"
  | .punct c => c.toString

def isWordStart (c : Char) : Bool := c.isAlpha || c == '_'
def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'
def isIntChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Lex one line of text (no newlines) into tokens and the trailing comment, if any. -/
partial def lexLine (cs : List Char) (acc : Array Tok) : Array Tok × Option String :=
  match cs with
  | [] => (acc, none)
  | ';' :: rest => (acc, some (String.ofList rest))
  | c :: rest =>
    if c == ' ' || c == '\t' || c == '\r' then lexLine rest acc
    else if c == '-' && rest.head? == some '>' then lexLine rest.tail (acc.push .arrow)
    else if (c == '-' || c == '+') && (rest.head?.map Char.isDigit |>.getD false) then
      let (ds, rest') := rest.span isIntChar
      lexLine rest' (acc.push (.int (String.ofList (c :: ds))))
    else if c.isDigit then
      let (ds, rest') := cs.span isIntChar
      lexLine rest' (acc.push (.int (String.ofList ds)))
    else if isWordStart c then
      let (ws, rest') := cs.span isWordChar
      lexLine rest' (acc.push (.word (String.ofList ws)))
    else if c == '%' then
      let (ws, rest') := rest.span isWordChar
      lexLine rest' (acc.push (.name (String.ofList ws)))
    else lexLine rest (acc.push (.punct c))

/-- Parse an integer literal: optional sign, decimal or `0x` hex with `_` separators. -/
def parseIntLit (s : String) : Option Int :=
  let cs := s.toList
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let mag : Option Nat := match cs with
    | '0' :: 'x' :: hs | '0' :: 'X' :: hs =>
      let hs := hs.filter (· != '_')
      if hs.isEmpty then none else
      hs.foldlM (init := 0) fun acc h =>
        if h.isDigit then some (acc * 16 + (h.toNat - '0'.toNat))
        else if 'a' ≤ h ∧ h ≤ 'f' then some (acc * 16 + (h.toNat - 'a'.toNat + 10))
        else if 'A' ≤ h ∧ h ≤ 'F' then some (acc * 16 + (h.toNat - 'A'.toNat + 10))
        else none
    | ds =>
      let ds := ds.filter (· != '_')
      if ds.isEmpty then none else
      ds.foldlM (init := 0) fun acc d =>
        if d.isDigit then some (acc * 10 + (d.toNat - '0'.toNat)) else none
  mag.map fun m => if neg then -(m : Int) else m

/-- `pre ++ digits` ↦ the number. -/
def numSuffix? (pre s : String) : Option Nat :=
  if s.startsWith pre then
    let d := (s.drop pre.length).toString
    if !d.isEmpty && d.all Char.isDigit then d.toNat? else none
  else none

/-! ## Parser monad -/

structure PState where
  pos : Nat := 0
  types : List (ValueId × Ty) := []
  aliases : List (ValueId × ValueId) := []
  externs : List (FnRef × ExtFunc) := []
  sigDecls : List (Nat × Signature) := []

abbrev P := ReaderT (Array Tok) (StateT PState (Except ParseError))

def malformed {α : Type} (msg : String) : P α := throw (.malformed msg)
def unsupported {α : Type} (msg : String) : P α := throw (.unsupported msg)

def peekAt (k : Nat) : P (Option Tok) := do
  let toks ← read
  return toks[(← get).pos + k]?

def peek : P (Option Tok) := peekAt 0

def advance : P Unit := modify fun s => { s with pos := s.pos + 1 }

def next : P Tok := do
  match ← peek with
  | some t => advance; return t
  | none => malformed "unexpected end of input"

def atEnd : P Bool := return (← peek).isNone

def describe : P String := do
  match ← peek with
  | some t => return s!"'{t.show}'"
  | none => return "end of input"

def expectPunct (c : Char) : P Unit := do
  match ← peek with
  | some (.punct d) => if c == d then advance else malformed s!"expected '{c}', got '{d}'"
  | _ => malformed s!"expected '{c}', got {← describe}"

def optPunct (c : Char) : P Bool := do
  match ← peek with
  | some (.punct d) => if c == d then advance; return true else return false
  | _ => return false

def isPunct (c : Char) : P Bool := do
  match ← peek with
  | some (.punct d) => return c == d
  | _ => return false

def expectWord (w : String) : P Unit := do
  match ← peek with
  | some (.word v) => if v == w then advance else malformed s!"expected '{w}', got '{v}'"
  | _ => malformed s!"expected '{w}', got {← describe}"

def optWord (w : String) : P Bool := do
  match ← peek with
  | some (.word v) => if v == w then advance; return true else return false
  | _ => return false

def anyWord : P String := do
  match ← next with
  | .word w => return w
  | t => malformed s!"expected identifier, got '{t.show}'"

def anyName : P String := do
  match ← next with
  | .name n => return n
  | t =>
    match t with
    | .word w => unsupported s!"function name '{w}' (only %names)"
    | _ => malformed s!"expected %name, got '{t.show}'"

def anyInt : P Int := do
  match ← next with
  | .int s =>
    match parseIntLit s with
    | some i => return i
    | none => malformed s!"bad integer literal '{s}'"
  | t => malformed s!"expected integer, got '{t.show}'"

/-- A numbered entity `preN`. -/
def entity (pre : String) : P Nat := do
  let w ← anyWord
  match numSuffix? pre w with
  | some n => return n
  | none => malformed s!"expected {pre}N, got '{w}'"

def isEntity (pre : String) (t : Option Tok) : Bool :=
  match t with
  | some (.word w) => (numSuffix? pre w).isSome
  | _ => false

/-- A type name. Non-integer types are `unsupported`. -/
def parseTyName (w : String) : P Ty :=
  match Ty.ofName? w with
  | some t => pure t
  | none =>
    if w.startsWith "i" || w.startsWith "f" then unsupported s!"type {w}"
    else malformed s!"expected a type, got '{w}'"

def ty : P Ty := do parseTyName (← anyWord)

/-- Optional offset `+N`/`-N` (the sign is mandatory, as in the reader). -/
def optOffset : P Int := do
  match ← peek with
  | some (.int s) =>
    if s.startsWith "+" || s.startsWith "-" then
      advance
      match parseIntLit s with
      | some i => return i
      | none => malformed s!"bad offset '{s}'"
    else return 0
  | _ => return 0

/-! ## Values -/

/-- Follow the alias map (filled for the whole function before its body is read, so
uses may precede the alias line). The map is checked acyclic by `collectAliases`. -/
def resolveAlias (v : ValueId) : P ValueId := do
  let al := (← get).aliases
  let rec go : Nat → ValueId → ValueId
    | 0, v => v
    | n + 1, v => match al.lookup v with
      | some w => go n w
      | none => v
  return go (al.length + 1) v

/-- Pre-scan the token stream for every alias `vA -> vB` (as cranelift-reader resolves
aliases after reading the whole function), rejecting duplicate aliases and cycles. -/
def collectAliases : P Unit := do
  let toks ← read
  let mut al : List (ValueId × ValueId) := []
  for i in [0:toks.size] do
    if let (some (.word a), some .arrow, some (.word b)) := (toks[i]?, toks[i+1]?, toks[i+2]?) then
      if let (some a, some b) := (numSuffix? "v" a, numSuffix? "v" b) then
        if (al.lookup a).isSome then malformed s!"v{a} is aliased twice"
        al := (a, b) :: al
  for (a, _) in al do
    let mut v := a
    for _ in [0:al.length] do
      match al.lookup v with
      | some w =>
        if w == a then malformed s!"alias cycle through v{a}"
        v := w
      | none => break
  modify fun s => { s with aliases := al }

/-- A value use (aliases resolved). -/
def value : P ValueId := do resolveAlias (← entity "v")

def typeOf (v : ValueId) : P Ty := do
  match (← get).types.lookup v with
  | some t => return t
  | none => malformed s!"cannot infer the type of v{v} (not yet defined)"

def defineValue (v : ValueId) (t : Ty) : P Unit :=
  modify fun s => { s with types := (v, t) :: s.types }

def commaSep {α : Type} (p : P α) (close : Char) : P (List α) := do
  if ← isPunct close then return []
  let mut out := #[← p]
  while ← optPunct ',' do
    out := out.push (← p)
  return out.toList

/-! ## Signatures and declarations -/

def abiParam : P AbiParam := do
  let t ← ty
  let mut ext := ArgExt.none
  let mut purpose := ArgPurpose.normal
  repeat
    match ← peek with
    | some (.word "uext") => advance; ext := .uext
    | some (.word "sext") => advance; ext := .sext
    | some (.word "vmctx") => advance; purpose := .vmctx
    | some (.word "sret") => advance; purpose := .sret
    | some (.word "sarg") =>
      advance; expectPunct '('
      let n ← anyInt
      expectPunct ')'
      purpose := .sarg n.toNat
    | _ => break
  return { ty := t, ext, purpose }

def signature : P Signature := do
  expectPunct '('
  let params ← commaSep abiParam ')'
  expectPunct ')'
  let returns ← match ← peek with
    | some .arrow => do advance; let r ← abiParam; let mut rs := #[r]
                        while ← optPunct ',' do rs := rs.push (← abiParam)
                        pure rs.toList
    | _ => pure []
  let callConv ← match ← peek with
    | some (.word w) =>
      match CallConv.ofName? w with
      | some cc => do advance; pure (some cc)
      | none => pure none
    | _ => pure none
  return { params, returns, callConv }

/-- Memory flags (a possibly empty sequence of flag words). -/
def memFlags : P MemFlags := do
  let mut f : MemFlags := {}
  repeat
    match ← peek with
    | some (.word "notrap") => advance; f := { f with trapCode := none }
    | some (.word "aligned") => advance; f := { f with aligned := true }
    | some (.word "readonly") => advance; f := { f with readonly := true }
    | some (.word "can_move") => advance; f := { f with canMove := true }
    | some (.word "little") => advance; f := { f with endianness := some .little }
    | some (.word "big") => advance; f := { f with endianness := some .big }
    | some (.word w) =>
      match TrapCode.ofName? w with
      | some c => advance; f := { f with trapCode := some c }
      | none => break
    | _ => break
  return f

def trapCode : P TrapCode := do
  let w ← anyWord
  match TrapCode.ofName? w with
  | some c => return c
  | none => malformed s!"unknown trap code '{w}'"

/-- Preamble declarations. -/
inductive Decl where
  | slot (id : SlotId) (s : StackSlot)
  | global (id : Nat) (g : GlobalValue)
  | extern (id : FnRef) (e : ExtFunc)
  | sigDecl (id : Nat) (s : Signature)

def decl : P Decl := do
  let t ← peek
  if isEntity "ss" t then
    let id ← entity "ss"
    expectPunct '='
    let kind ← anyWord
    if kind != "explicit_slot" then unsupported s!"stack slot kind {kind}"
    let size ← anyInt
    let mut align := none
    if ← optPunct ',' then
      expectWord "align"; expectPunct '='
      align := some (← anyInt).toNat
    return .slot id { size := size.toNat, align }
  else if isEntity "gv" t then
    let id ← entity "gv"
    expectPunct '='
    match ← anyWord with
    | "vmctx" => return .global id .vmctx
    | "load" =>
      expectPunct '.'
      let t ← ty
      let flags ← memFlags
      let base ← entity "gv"
      let off ← optOffset
      return .global id (.load t flags base off)
    | "iadd_imm" =>
      expectPunct '.'
      let t ← ty
      let base ← entity "gv"
      expectPunct ','
      let off ← anyInt
      return .global id (.iaddImm t base off)
    | "symbol" =>
      let colocated ← optWord "colocated"
      if ← optWord "tls" then unsupported "tls symbol global value"
      let n ← anyName
      let off ← optOffset
      return .global id (.symbol n off colocated)
    | w => unsupported s!"global value kind {w}"
  else if isEntity "sig" t then
    let id ← entity "sig"
    expectPunct '='
    let s ← signature
    -- cg_clif re-declares the same `sigN` per call_indirect site; keep the first (the
    -- printer would emit a duplicate entity, which the pinned reader rejects). step 5.
    if !((← get).sigDecls.any fun d => d.1 == id) then
      modify fun st => { st with sigDecls := (id, s) :: st.sigDecls }
    return .sigDecl id s
  else if isEntity "fn" t then
    let id ← entity "fn"
    expectPunct '='
    let colocated ← optWord "colocated"
    if ← optWord "patchable" then unsupported "patchable function reference"
    let n ← anyName
    if !(← isPunct '(') then unsupported s!"fn{id} = %{n} with a signature reference"
    let sig ← signature
    let e : ExtFunc := { name := n, sig, colocated }
    modify fun s => { s with externs := (id, e) :: s.externs }
    return .extern id e
  else
    match t with
    | some (.word w) => unsupported s!"declaration '{w}'"
    | _ => malformed s!"expected a declaration, got {← describe}"

/-! ## Instructions -/

def blockCall : P BlockCall := do
  let b ← entity "block"
  if ← optPunct '(' then
    let args ← commaSep value ')'
    expectPunct ')'
    return { block := b, args }
  return { block := b }

def unaryOp? : String → Option UnaryOp
  | "ineg" => some .ineg | "bnot" => some .bnot | "iabs" => some .iabs | "clz" => some .clz
  | "ctz" => some .ctz | "cls" => some .cls | "popcnt" => some .popcnt
  | "bitrev" => some .bitrev | "bswap" => some .bswap | _ => none

def binaryOp? : String → Option BinaryOp
  | "iadd" => some .iadd | "isub" => some .isub | "imul" => some .imul
  | "umulhi" => some .umulhi | "smulhi" => some .smulhi
  | "band" => some .band | "bor" => some .bor | "bxor" => some .bxor
  | "ishl" => some .ishl | "ushr" => some .ushr | "sshr" => some .sshr
  | "rotl" => some .rotl | "rotr" => some .rotr
  | "smin" => some .smin | "smax" => some .smax | "umin" => some .umin | "umax" => some .umax
  | "uadd_sat" => some .uaddSat | "sadd_sat" => some .saddSat
  | "usub_sat" => some .usubSat | "ssub_sat" => some .ssubSat
  | _ => none

def divOp? : String → Option DivOp
  | "udiv" => some .udiv | "sdiv" => some .sdiv | "urem" => some .urem | "srem" => some .srem
  | _ => none

def overflowOp? : String → Option OverflowOp
  | "uadd_overflow" => some .uaddOverflow | "sadd_overflow" => some .saddOverflow
  | "usub_overflow" => some .usubOverflow | "ssub_overflow" => some .ssubOverflow
  | "umul_overflow" => some .umulOverflow | "smul_overflow" => some .smulOverflow
  | _ => none

def carryOp? : String → Option CarryOp
  | "uadd_overflow_cin" => some .uaddOverflowCin | "sadd_overflow_cin" => some .saddOverflowCin
  | "usub_overflow_bin" => some .usubOverflowBin | "ssub_overflow_bin" => some .ssubOverflowBin
  | _ => none

def loadOp? : String → Option LoadOp
  | "load" => some .load | "uload8" => some .uload8 | "sload8" => some .sload8
  | "uload16" => some .uload16 | "sload16" => some .sload16
  | "uload32" => some .uload32 | "sload32" => some .sload32 | _ => none

def storeOp? : String → Option StoreOp
  | "store" => some .store | "istore8" => some .istore8 | "istore16" => some .istore16
  | "istore32" => some .istore32 | _ => none

/-- The controlling type: the explicit suffix, else the type of the typevar operand. -/
def ctrl (explicit : Option Ty) (v : ValueId) : P Ty := do
  match explicit with
  | some t => return t
  | none => typeOf v

def needTy (op : String) (explicit : Option Ty) : P Ty := do
  match explicit with
  | some t => return t
  | none => malformed s!"{op} needs a type suffix"

/-- Body item: an instruction or a terminator. -/
inductive Item where
  | inst (i : Inst)
  | term (t : Terminator)

def item (op : String) (sfx : Option Ty) : P Item := do
  if let some u := unaryOp? op then
    let x ← value
    return .inst (.unary u (← ctrl sfx x) x)
  if let some b := binaryOp? op then
    let x ← value; expectPunct ','; let y ← value
    return .inst (.binary b (← ctrl sfx x) x y)
  if let some d := divOp? op then
    let x ← value; expectPunct ','; let y ← value
    return .inst (.div d (← ctrl sfx x) x y)
  if let some o := overflowOp? op then
    let x ← value; expectPunct ','; let y ← value
    return .inst (.overflow o (← ctrl sfx x) x y)
  if let some c := carryOp? op then
    let x ← value; expectPunct ','; let y ← value; expectPunct ','; let c' ← value
    return .inst (.carry c (← ctrl sfx x) x y c')
  if let some l := loadOp? op then
    let t ← needTy op sfx
    let flags ← memFlags
    let p ← value
    let off ← optOffset
    return .inst (.load l t flags p off)
  if let some s := storeOp? op then
    let flags ← memFlags
    let x ← value; expectPunct ','; let p ← value
    let off ← optOffset
    return .inst (.store s (← ctrl sfx x) flags x p off)
  match op with
  | "iconst" =>
    let t ← needTy op sfx
    if t == .i128 then malformed "iconst.i128 is not valid CLIF"
    let i ← anyInt
    return .inst (.iconst t (BitVec.ofInt t.width i))
  | "uadd_overflow_trap" =>
    let x ← value; expectPunct ','; let y ← value; expectPunct ','
    let c ← trapCode
    return .inst (.uaddOverflowTrap (← ctrl sfx x) x y c)
  | "icmp" =>
    let w ← anyWord
    let cc ← match IntCC.ofName? w with
      | some cc => pure cc
      | none => malformed s!"unknown condition code '{w}'"
    let x ← value; expectPunct ','; let y ← value
    return .inst (.icmp cc (← ctrl sfx x) x y)
  | "select" | "select_spectre_guard" | "bitselect" =>
    let c ← value; expectPunct ','; let x ← value; expectPunct ','; let y ← value
    let t ← if op == "bitselect" then ctrl sfx c else ctrl sfx x
    return .inst (match op with
      | "select" => .select t c x y
      | "select_spectre_guard" => .selectSpectreGuard t c x y
      | _ => .bitselect t c x y)
  | "bmask" => let t ← needTy op sfx; return .inst (.bmask t (← value))
  | "uextend" => let t ← needTy op sfx; return .inst (.extend .uextend t (← value))
  | "sextend" => let t ← needTy op sfx; return .inst (.extend .sextend t (← value))
  | "ireduce" => let t ← needTy op sfx; return .inst (.ireduce t (← value))
  | "iconcat" =>
    let lo ← value; expectPunct ','; let hi ← value
    return .inst (.iconcat (← ctrl sfx lo) lo hi)
  | "isplit" => let x ← value; return .inst (.isplit (← ctrl sfx x) x)
  | "stack_addr" =>
    let t ← needTy op sfx
    let s ← entity "ss"
    let off ← optOffset
    return .inst (.stackAddr t s off)
  | "symbol_value" =>
    let t ← needTy op sfx
    return .inst (.symbolValue t (← entity "gv"))
  | "call" =>
    let f ← entity "fn"
    expectPunct '('
    let args ← commaSep value ')'
    expectPunct ')'
    return .inst (.call f args)
  | "call_indirect" =>
    let t := sfx.getD .i64
    let sig ← entity "sig"
    expectPunct ','
    let callee ← value
    expectPunct '('
    let args ← commaSep value ')'
    expectPunct ')'
    return .inst (.callIndirect sig callee args)
  | "func_addr" =>
    let t ← needTy op sfx
    return .inst (.funcAddr t (← entity "fn"))
  | "atomic_rmw" =>
    let t ← needTy op sfx
    let flags ← memFlags
    let w ← anyWord
    let rop ← match AtomicRmwOp.ofName? w with
      | some o => pure o
      | none => malformed s!"unknown atomic_rmw operation '{w}'"
    let p ← value; expectPunct ','; let x ← value
    return .inst (.atomicRmw rop t flags p x)
  | "atomic_cas" =>
    let flags ← memFlags
    let p ← value; expectPunct ','; let e ← value; expectPunct ','; let x ← value
    return .inst (.atomicCas (← ctrl sfx e) flags p e x)
  | "atomic_load" =>
    let t ← needTy op sfx
    let flags ← memFlags
    return .inst (.atomicLoad t flags (← value))
  | "atomic_store" =>
    let flags ← memFlags
    let x ← value; expectPunct ','; let p ← value
    return .inst (.atomicStore (← ctrl sfx x) flags x p)
  | "fence" => return .inst .fence
  | "bitcast" =>
    let t ← needTy op sfx
    let flags ← memFlags
    return .inst (.bitcast t flags (← value))
  | "return_call" =>
    let f ← entity "fn"
    expectPunct '('
    let args ← commaSep value ')'
    expectPunct ')'
    return .term (.returnCall f args)
  | "trapz" => let c ← value; expectPunct ','; return .inst (.trapz c (← trapCode))
  | "trapnz" => let c ← value; expectPunct ','; return .inst (.trapnz c (← trapCode))
  | "nop" => return .inst .nop
  | "jump" => return .term (.jump (← blockCall))
  | "brif" =>
    let c ← value; expectPunct ','; let t ← blockCall; expectPunct ','; let e ← blockCall
    return .term (.brif c t e)
  | "br_table" =>
    let x ← value; expectPunct ','
    let d ← blockCall; expectPunct ','
    expectPunct '['
    let tbl ← commaSep blockCall ']'
    expectPunct ']'
    return .term (.brTable x d tbl)
  | "return" =>
    -- `return` ends the block: its operands are values up to the next block/`}`.
    if isEntity "v" (← peek) then
      let vs ← commaSep value '}'
      return .term (.ret vs)
    return .term (.ret [])
  | "trap" => return .term (.trap (← trapCode))
  | _ => unsupported s!"opcode {op}"

/-- Result types of an instruction in the current parser state. -/
def resultTypes (i : Inst) : P (List Ty) := do
  let ext := (← get).externs
  let sigs := (← get).sigDecls
  match i.resultTypes (fun r => (ext.lookup r).map (·.sig)) (fun s => (sigs.lookup s)) with
  | some ts => return ts
  | none => malformed "cannot determine the result types of an instruction"

/-- One body line: alias, instruction (with results) or terminator. -/
def bodyLine : P (Option (Sum Stmt Terminator)) := do
  -- alias `vA -> vB`
  if isEntity "v" (← peek) && (← peekAt 1) == some .arrow then
    -- already recorded by `collectAliases`; uses resolve through the alias map
    let _ ← entity "v"; advance
    let _ ← entity "v"
    return none
  let results ←
    if isEntity "v" (← peek) then do
      let rs ← commaSep (entity "v") '='
      expectPunct '='
      pure rs
    else pure []
  let op ← anyWord
  let sfx ← if ← optPunct '.' then some <$> ty else pure none
  match ← item op sfx with
  | .inst i =>
    let tys ← resultTypes i
    if tys.length != results.length then
      malformed s!"{op}: {results.length} results given, {tys.length} expected"
    for (r, t) in results.zip tys do defineValue r t
    return some (.inl { results, inst := i })
  | .term t =>
    if !results.isEmpty then malformed s!"{op} has no results"
    return some (.inr t)

def blockParam : P (ValueId × Ty) := do
  let v ← entity "v"; expectPunct ':'
  let t ← ty
  defineValue v t
  return (v, t)

def block : P Block := do
  let id ← entity "block"
  let params ← if ← optPunct '(' then do
      let ps ← commaSep blockParam ')'
      expectPunct ')'
      pure ps
    else pure []
  let cold ← optWord "cold"
  expectPunct ':'
  let mut body := #[]
  repeat
    match ← bodyLine with
    | none => pure ()
    | some (.inl s) => body := body.push s
    | some (.inr t) => return { id, params, cold, body := body.toList, term := t }
    if (← atEnd) || (← isPunct '}') || isEntity "block" (← peek) then
      break
  malformed s!"block{id} has no terminator"

/-- `function %name sig { decls blocks }` -/
def function : P Function := do
  collectAliases
  expectWord "function"
  let name ← anyName
  let sig ← signature
  expectPunct '{'
  let mut slots := #[]
  let mut globals := #[]
  let mut externs := #[]
  let mut sigDecls := #[]
  while !(isEntity "block" (← peek)) && !(← isPunct '}') do
    match ← decl with
    | .slot i s => slots := slots.push (i, s)
    | .global i g => globals := globals.push (i, g)
    | .extern i e => externs := externs.push (i, e)
    | .sigDecl i s => sigDecls := sigDecls.push (i, s)
  let mut blocks := #[]
  while !(← isPunct '}') do
    blocks := blocks.push (← block)
  expectPunct '}'
  if !(← atEnd) then malformed s!"unexpected {← describe} after function body"
  return { name, sig, slots := slots.toList, globals := globals.toList,
           externs := externs.toList, sigDecls := sigDecls.toList, blocks := blocks.toList }

/-! ## Run commands -/

def dataValue (t : Ty) : P Val := do
  match ← next with
  | .int s =>
    match parseIntLit s with
    | some i => return Val.ofInt t i
    | none => malformed s!"bad {t.name} value '{s}'"
  | tok => malformed s!"expected an {t.name} value, got '{tok.show}'"

def dataValues (tys : List Ty) : P (List Val) := do
  let mut out := #[]
  let mut first := true
  for t in tys do
    if !first then expectPunct ','
    first := false
    out := out.push (← dataValue t)
  return out.toList

def runCommand (sig : Signature) (attached : String) : P RunCommand := do
  let kw ← anyWord
  let ptys := sig.params.map (·.ty)
  let rtys := sig.returns.map (·.ty)
  let invocation : P (String × List Val) := do
    let f ← anyName
    expectPunct '('
    let args ← dataValues ptys
    expectPunct ')'
    return (f, args)
  if kw == "run" then
    if ← optPunct ':' then
      let (f, args) ← invocation
      let isEq ← if ← optPunct '=' then do expectPunct '='; pure true
        else if ← optPunct '!' then do expectPunct '='; pure false
        else malformed "expected == or !="
      let multi := rtys.length != 1
      if multi then expectPunct '['
      let vals ← dataValues rtys
      if multi then expectPunct ']'
      if !(← atEnd) then malformed s!"trailing {← describe} in run command"
      return { func := f, args, expect := if isEq then .eq vals else .ne vals }
    else if ptys.isEmpty && rtys.length == 1 then
      return { func := attached, expect := .nonzero }
    else malformed "bare `run` needs a function `() -> iN`"
  else
    if ← optPunct ':' then
      let (f, args) ← invocation
      return { func := f, args, expect := .print }
    else if ptys.isEmpty then
      return { func := attached, expect := .print }
    else malformed "bare `print` needs a function without parameters"

/-- If `text` (a comment body) is a run/print command, parse it. -/
def runComment (sig : Signature) (attached : String) (text : String) :
    Except ParseError (Option RunCommand) :=
  let trimmed := text.toList.dropWhile (fun c => c == ' ' || c == ';')
  let toks : Array Tok := (lexLine trimmed #[]).1
  match toks[0]? with
  | some (Tok.word "run") | some (Tok.word "print") =>
    match (runCommand sig attached).run toks |>.run {} with
    | .ok (r, _) => .ok (some r)
    | .error e => .error e
  | _ => .ok none

end Parse

/-! ## Files -/

/-- One function of a file: its name and either the parsed function (with its run
commands) or the reason it is not parsed. `runLines` counts its run/print comments. -/
structure ParsedFunction where
  name : String
  func : Except ParseError Function
  runLines : Nat

structure ParsedFile where
  header : List String
  /-- The `; data:` directives of the header (or the first malformed one). -/
  data : Except String (List DataObject) := .ok []
  funcs : List ParsedFunction

/-! ## Data directives

`; data: %name [align=N] [writable] = item item ...` before the first function declares a
link-time data object (`Clif.DataObject`). An item is either an even-length string of hex
digits (bytes in memory order, e.g. `deadbeef` = bytes `de ad be ef`) or `%sym[+N|-N]`
(8-byte little-endian absolute address of data object `sym` plus the addend). -/

def hexDigit? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def hexBytes? : List Char → Option (List (BitVec 8))
  | [] => some []
  | h :: l :: rest => do
    let a ← hexDigit? h
    let b ← hexDigit? l
    let r ← hexBytes? rest
    pure (BitVec.ofNat 8 (16 * a + b) :: r)
  | [_] => none

def dataItems (w : String) : Except String (List DataItem) :=
  if w.startsWith "%" then
    let body := (w.drop 1).toString
    let (n, off) := match body.splitOn "+", body.splitOn "-" with
      | [n, o], _ => (n, (Parse.parseIntLit o))
      | _, [n, o] => (n, (Parse.parseIntLit o).map (- ·))
      | _, _ => (body, some 0)
    match off with
    | some o => if n.isEmpty then .error s!"bad data item {w}" else .ok [.addr n o]
    | none => .error s!"bad addend in data item {w}"
  else match hexBytes? w.toList with
    | some bs => .ok (bs.map .byte)
    | none => .error s!"bad data item {w} (expected hex bytes or %sym[+N])"

/-- If the comment body `text` is a `data:` directive, parse it. -/
def dataDirective (text : String) : Option (Except String DataObject) :=
  let t := (String.ofList (text.toList.dropWhile (fun c => c == ' ' || c == ';'))).trimAscii.toString
  if !t.startsWith "data:" then none else some do
    let ws := ((t.drop 5).toString.splitOn " ").filter (!·.isEmpty)
    match ws with
    | nm :: rest =>
      if !nm.startsWith "%" || nm.length < 2 then throw s!"data: expected %name, got {nm}"
      let mut o : DataObject := { name := (nm.drop 1).toString, items := [] }
      let mut rest := rest
      let mut done := false
      while !done do
        match rest with
        | "writable" :: r => o := { o with writable := true }; rest := r
        | "=" :: r => rest := r; done := true
        | w :: r =>
          if w.startsWith "align=" then
            match (w.drop 6).toString.toNat? with
            | some a => if a == 0 then throw "data: align must be positive"
                        o := { o with align := a }; rest := r
            | none => throw s!"data: bad {w}"
          else throw s!"data: unexpected {w}"
        | [] => throw "data: missing '='"
      let mut items := #[]
      for w in rest do
        items := items ++ (← dataItems w).toArray
      pure { o with items := items.toList }
    | [] => throw "data: missing name"

def isFunctionLine (l : String) : Bool :=
  let t := l.trimAscii.toString
  t == "function" || t.startsWith "function " || t.startsWith "function%"

/-- Is this comment body a run/print command? -/
def isRunComment (text : String) : Bool :=
  let trimmed := text.toList.dropWhile (fun c => c == ' ' || c == ';')
  let toks : Array Parse.Tok := (Parse.lexLine trimmed #[]).1
  match toks[0]? with
  | some (Parse.Tok.word "run") | some (Parse.Tok.word "print") => true
  | _ => false

/-- Parse one function chunk (from its `function` line up to the next function). -/
def parseChunk (lines : List String) : ParsedFunction := Id.run do
  let mut toks : Array Parse.Tok := #[]
  let mut comments : Array String := #[]
  for l in lines do
    let (ts, c) := Parse.lexLine l.toList toks
    toks := ts
    if let some c := c then comments := comments.push c
  let runLines := (comments.filter isRunComment).size
  let name := match (toks[1]? : Option Parse.Tok) with
    | some (.name n) => n
    | _ => "?"
  match (Parse.function.run toks |>.run {}) with
  | .error e => return { name, func := .error e, runLines }
  | .ok (f, _) =>
    let mut runs := #[]
    for c in comments do
      match Parse.runComment f.sig f.name c with
      | .ok (some r) => runs := runs.push r
      | .ok none => pure ()
      | .error e => return { name, func := .error e, runLines }
    return { name, func := .ok { f with runs := runs.toList }, runLines }

/-- Parse a `.clif` file function by function. -/
def parseFile (src : String) : ParsedFile := Id.run do
  let lines := src.splitOn "\n"
  let mut header := #[]
  let mut data : Except String (Array DataObject) := .ok #[]
  let mut chunks : Array (Array String) := #[]
  for l in lines do
    if isFunctionLine l then
      chunks := chunks.push #[l]
    else if chunks.isEmpty then
      let t := (l.toList.takeWhile (· != ';') |> String.ofList).trimAscii.toString
      if !t.isEmpty then header := header.push t
      let c := l.toList.dropWhile (· != ';')
      if !c.isEmpty then
        match dataDirective (String.ofList c), data with
        | some (.ok o), .ok ds => data := .ok (ds.push o)
        | some (.error e), .ok _ => data := .error e
        | _, _ => pure ()
    else
      chunks := chunks.modify (chunks.size - 1) (·.push l)
  return { header := header.toList, data := data.map (·.toList),
           funcs := chunks.toList.map (parseChunk ·.toList) }

/-- Parse a `.clif` file; every function must be in subset S. -/
def parse (src : String) : Except String Program := do
  let pf := parseFile src
  let data ← pf.data
  let mut funcs := #[]
  for f in pf.funcs do
    match f.func with
    | .ok fn => funcs := funcs.push fn
    | .error e => throw s!"%{f.name}: {e}"
  return { header := pf.header, data, funcs := funcs.toList }

end Clif
