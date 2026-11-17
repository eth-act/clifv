import FV.Clif.Syntax
import FV.Clif.FloatLit

/-!
# CLIF text printer

`Clif.print : Program → String` produces text accepted by `cranelift-reader` 0.136.1.
Every polymorphic instruction is printed with an explicit `.ty` suffix (so the reader never
has to infer a controlling type from a value defined later in the layout); the suffix of
`brif`/`trapz`/`trapnz` is the type of the condition. Run commands are printed as
`; run: ...` comments after their function. Integers are printed in signed decimal, floats in
Cranelift's hexadecimal float form (`Clif.FloatLit.format`).
-/

namespace Clif

namespace Print

def UnaryOp.name : UnaryOp → String
  | .ineg => "ineg" | .bnot => "bnot" | .iabs => "iabs" | .clz => "clz" | .ctz => "ctz"
  | .cls => "cls" | .popcnt => "popcnt" | .bitrev => "bitrev" | .bswap => "bswap"

def BinaryOp.name : BinaryOp → String
  | .iadd => "iadd" | .isub => "isub" | .imul => "imul"
  | .umulhi => "umulhi" | .smulhi => "smulhi"
  | .band => "band" | .bor => "bor" | .bxor => "bxor"
  | .ishl => "ishl" | .ushr => "ushr" | .sshr => "sshr" | .rotl => "rotl" | .rotr => "rotr"
  | .smin => "smin" | .smax => "smax" | .umin => "umin" | .umax => "umax"
  | .uaddSat => "uadd_sat" | .saddSat => "sadd_sat"
  | .usubSat => "usub_sat" | .ssubSat => "ssub_sat"

def DivOp.name : DivOp → String
  | .udiv => "udiv" | .sdiv => "sdiv" | .urem => "urem" | .srem => "srem"

def OverflowOp.name : OverflowOp → String
  | .uaddOverflow => "uadd_overflow" | .saddOverflow => "sadd_overflow"
  | .usubOverflow => "usub_overflow" | .ssubOverflow => "ssub_overflow"
  | .umulOverflow => "umul_overflow" | .smulOverflow => "smul_overflow"

def CarryOp.name : CarryOp → String
  | .uaddOverflowCin => "uadd_overflow_cin" | .saddOverflowCin => "sadd_overflow_cin"
  | .usubOverflowBin => "usub_overflow_bin" | .ssubOverflowBin => "ssub_overflow_bin"

def LoadOp.name : LoadOp → String
  | .load => "load" | .uload8 => "uload8" | .sload8 => "sload8" | .uload16 => "uload16"
  | .sload16 => "sload16" | .uload32 => "uload32" | .sload32 => "sload32"

def StoreOp.name : StoreOp → String
  | .store => "store" | .istore8 => "istore8" | .istore16 => "istore16"
  | .istore32 => "istore32"

def v (x : ValueId) : String := s!"v{x}"

def vs (xs : List ValueId) : String := ", ".intercalate (xs.map v)

def offset (i : Int) : String :=
  if i == 0 then "" else if i > 0 then s!"+{i}" else s!"{i}"

def memFlags (f : MemFlags) : String := Id.run do
  let mut out := ""
  match f.trapCode with
  | none => out := out ++ " notrap"
  | some .heapOob => pure ()
  | some c => out := out ++ " " ++ c.name
  if f.aligned then out := out ++ " aligned"
  if f.readonly then out := out ++ " readonly"
  if f.canMove then out := out ++ " can_move"
  match f.endianness with
  | some .big => out := out ++ " big"
  | some .little => out := out ++ " little"
  | none => pure ()
  return out

def blockCall (b : BlockCall) : String :=
  if b.args.isEmpty then s!"block{b.block}" else s!"block{b.block}({vs b.args})"

def tryArg : TryArg → String
  | .val x => v x
  | .ret i => s!"ret{i}"
  | .exn i => s!"exn{i}"

def tryDest (d : TryDest) : String :=
  if d.args.isEmpty then s!"block{d.block}"
  else s!"block{d.block}({", ".intercalate (d.args.map tryArg)})"

/-- `sigN, normal, [ items ]` (Cranelift's `DisplayExceptionTable`). -/
def exnTable (et : ExnTable) : String :=
  let items := et.items.map fun
    | .tag n d => s!"tag{n}: {tryDest d}"
    | .default d => s!"default: {tryDest d}"
    | .context x => s!"context {v x}"
  let body := if items.isEmpty then "[]" else s!"[ {", ".intercalate items} ]"
  s!"sig{et.sig}, {tryDest et.normal}, {body}"

def abiParam (p : AbiParam) : String :=
  let ext := match p.ext with
    | .none => "" | .uext => " uext" | .sext => " sext"
  let purpose := match p.purpose with
    | .normal => "" | .vmctx => " vmctx" | .sret => " sret" | .sarg n => s!" sarg({n})"
  p.ty.name ++ ext ++ purpose

def signature (s : Signature) : String :=
  let ps := "(" ++ ", ".intercalate (s.params.map abiParam) ++ ")"
  let rs := if s.returns.isEmpty then "" else
    " -> " ++ ", ".intercalate (s.returns.map abiParam)
  let cc := match s.callConv with
    | none => ""
    | some c => " " ++ c.name
  ps ++ rs ++ cc

/-- Suffix `.ty` for a value's type, if known. -/
def sfxOf (tys : ValueId → Option Ty) (x : ValueId) : String :=
  match tys x with
  | some t => "." ++ t.name
  | none => ""

/-- Cranelift's text of the bits `x` of a float type of width `w`. -/
def floatText (w : Nat) (x : BitVec w) : String :=
  let (e, t) := FloatLit.fields w
  FloatLit.format x.toNat e t

def inst (tys : ValueId → Option Ty) : Inst → String
  | .iconst ty imm =>
    if ty.isFloat then s!"{ty.name}const {floatText ty.width imm}"
    else s!"iconst.{ty.name} {imm.toInt}"
  | .unary op ty x => s!"{UnaryOp.name op}.{ty.name} {v x}"
  | .binary op ty x y => s!"{BinaryOp.name op}.{ty.name} {v x}, {v y}"
  | .div op ty x y => s!"{DivOp.name op}.{ty.name} {v x}, {v y}"
  | .overflow op ty x y => s!"{OverflowOp.name op}.{ty.name} {v x}, {v y}"
  | .carry op ty x y c => s!"{CarryOp.name op}.{ty.name} {v x}, {v y}, {v c}"
  | .uaddOverflowTrap ty x y c => s!"uadd_overflow_trap.{ty.name} {v x}, {v y}, {c.name}"
  | .icmp cc ty x y => s!"icmp.{ty.name} {cc.name} {v x}, {v y}"
  | .select ty c x y => s!"select.{ty.name} {v c}, {v x}, {v y}"
  | .selectSpectreGuard ty c x y => s!"select_spectre_guard.{ty.name} {v c}, {v x}, {v y}"
  | .bitselect ty c x y => s!"bitselect.{ty.name} {v c}, {v x}, {v y}"
  | .bmask ty x => s!"bmask.{ty.name} {v x}"
  | .extend .uextend ty x => s!"uextend.{ty.name} {v x}"
  | .extend .sextend ty x => s!"sextend.{ty.name} {v x}"
  | .ireduce ty x => s!"ireduce.{ty.name} {v x}"
  | .iconcat ty lo hi => s!"iconcat.{ty.name} {v lo}, {v hi}"
  | .isplit ty x => s!"isplit.{ty.name} {v x}"
  | .load op ty f p off => s!"{LoadOp.name op}.{ty.name}{memFlags f} {v p}{offset off}"
  | .store op ty f x p off =>
    s!"{StoreOp.name op}.{ty.name}{memFlags f} {v x}, {v p}{offset off}"
  | .stackAddr ty s off => s!"stack_addr.{ty.name} ss{s}{offset off}"
  | .symbolValue ty gv => s!"symbol_value.{ty.name} gv{gv}"
  | .tlsValue ty gv => s!"tls_value.{ty.name} gv{gv}"
  | .funcAddr ty f => s!"func_addr.{ty.name} fn{f}"
  | .call f args => s!"call fn{f}({vs args})"
  | .callIndirect sig callee args =>
    s!"call_indirect sig{sig}, {v callee}({vs args})"
  | .atomicRmw op ty f p x => s!"atomic_rmw.{ty.name}{memFlags f} {op.name} {v p}, {v x}"
  | .atomicCas ty f p e x => s!"atomic_cas.{ty.name}{memFlags f} {v p}, {v e}, {v x}"
  | .atomicLoad ty f p => s!"atomic_load.{ty.name}{memFlags f} {v p}"
  | .atomicStore ty f x p => s!"atomic_store.{ty.name}{memFlags f} {v x}, {v p}"
  | .fence => "fence"
  | .bitcast ty f x => s!"bitcast.{ty.name}{memFlags f} {v x}"
  | .trapz c code => s!"trapz{sfxOf tys c} {v c}, {code.name}"
  | .trapnz c code => s!"trapnz{sfxOf tys c} {v c}, {code.name}"
  | .nop => "nop"
  | .float (.fcmp cc) ty args => s!"fcmp.{ty.name} {cc.name} {vs args}"
  | .float op ty args => s!"{op.name}.{ty.name} {vs args}"

def term (tys : ValueId → Option Ty) : Terminator → String
  | .jump b => s!"jump {blockCall b}"
  | .brif c t e => s!"brif{sfxOf tys c} {v c}, {blockCall t}, {blockCall e}"
  | .brTable x d tbl =>
    s!"br_table {v x}, {blockCall d}, [{", ".intercalate (tbl.map blockCall)}]"
  | .ret [] => "return"
  | .ret xs => s!"return {vs xs}"
  | .returnCall f args => s!"return_call fn{f}({vs args})"
  | .trap c => s!"trap {c.name}"
  | .tryCall f args et => s!"try_call fn{f}({vs args}), {exnTable et}"
  | .tryCallIndirect c args et => s!"try_call_indirect {v c}({vs args}), {exnTable et}"

def stmt (tys : ValueId → Option Ty) (s : Stmt) : String :=
  if s.results.isEmpty then inst tys s.inst else s!"{vs s.results} = {inst tys s.inst}"

def block (tys : ValueId → Option Ty) (b : Block) : String :=
  let params := if b.params.isEmpty then "" else
    "(" ++ ", ".intercalate (b.params.map fun (x, t) => s!"{v x}: {t.name}") ++ ")"
  let hdr := s!"block{b.id}{params}{if b.cold then " cold" else ""}:\n"
  hdr ++ String.join (b.body.map fun s => "    " ++ stmt tys s ++ "\n") ++
    "    " ++ term tys b.term ++ "\n"

def globalValue : GlobalValue → String
  | .vmctx => "vmctx"
  | .load ty f base off => s!"load.{ty.name}{memFlags f} gv{base}{offset off}"
  | .iaddImm ty base off => s!"iadd_imm.{ty.name} gv{base}, {off}"
  | .symbol n off col => s!"symbol {if col then "colocated " else ""}%{n}{offset off}"
  | .tlsSymbol n off col => s!"symbol {if col then "colocated " else ""}tls %{n}{offset off}"

def dataValue (x : Val) : String :=
  if x.ty.isFloat then floatText x.ty.width x.bits else toString x.toInt

def runCommand (sig : Signature) (r : RunCommand) : String :=
  let inv := s!"%{r.func}({", ".intercalate (r.args.map dataValue)})"
  let vals (xs : List Val) : String :=
    let body := ", ".intercalate (xs.map dataValue)
    if sig.returns.length == 1 then body else s!"[{body}]"
  match r.expect with
  | .eq xs => s!"; run: {inv} == {vals xs}"
  | .ne xs => s!"; run: {inv} != {vals xs}"
  | .nonzero => "; run"
  | .print => s!"; print: {inv}"

end Print

/-- Types of the values defined in a function (block parameters and results). -/
def Function.valueTypes (f : Function) : List (ValueId × Ty) :=
  f.blocks.flatMap fun b =>
    b.params ++ b.body.flatMap fun s =>
      match s.inst.resultTypes (fun r => (f.externs.lookup r).map (·.sig)) (fun _ => none) with
      | some ts => s.results.zip ts
      | none => []

def Function.print (f : Function) : String :=
  let tyMap := f.valueTypes
  let tys : ValueId → Option Ty := fun x => tyMap.lookup x
  let decls :=
    f.slots.map (fun (i, s) =>
      s!"    ss{i} = explicit_slot {s.size}" ++
        (match s.align with | some a => s!", align = {a}" | none => "")) ++
    f.globals.map (fun (i, g) => s!"    gv{i} = {Print.globalValue g}") ++
    -- Explicit `sigN` declarations before the `fnN` decls: a `fn` decl with an inline
    -- signature implicitly imports a signature at the next free index, so an explicit
    -- decl printed after it collides ("duplicate entity: sigN" in the pinned reader).
    f.sigDecls.map (fun (i, s) => s!"    sig{i} = {Print.signature s}") ++
    f.externs.map (fun (i, e) =>
      s!"    fn{i} = {if e.colocated then "colocated " else ""}%{e.name}{Print.signature e.sig}")
  let declText := if decls.isEmpty then "" else String.join (decls.map (· ++ "\n")) ++ "\n"
  let body := "\n".intercalate (f.blocks.map (Print.block tys))
  let runs := String.join (f.runs.map fun r => Print.runCommand f.sig r ++ "\n")
  s!"function %{f.name}{Print.signature f.sig} \{\n{declText}{body}}\n{runs}"

/-- Print a program as a `.clif` file. -/
def hexByte (b : BitVec 8) : String :=
  let d := fun (n : Nat) => "0123456789abcdef".toList.getD n '0'
  String.ofList [d (b.toNat / 16), d (b.toNat % 16)]

/-- Items as `; data:` tokens: runs of bytes as one hex token, relocations as `%sym[+N]`. -/
def printDataItems : List DataItem → List String
  | [] => []
  | .addr n off :: is =>
    (s!"%{n}" ++ (if off == 0 then "" else if off > 0 then s!"+{off}" else s!"{off}")) ::
      printDataItems is
  | .byte b :: is =>
    match printDataItems is with
    | t :: ts => if t.startsWith "%" then hexByte b :: t :: ts else (hexByte b ++ t) :: ts
    | [] => [hexByte b]

/-- The token of an address item (`printDataItems`' `.addr` case). -/
def addrToken (n : String) (off : Int) : String :=
  s!"%{n}" ++ (if off == 0 then "" else if off > 0 then s!"+{off}" else s!"{off}")

/-- `printDataItems` left to right in constant stack depth: the current run of bytes (`run`, its
hex digits) is appended to in place and closed at an address item or the end (`printDataItems_eq_TR`,
the compiler's implementation of `printDataItems`, which prepends each byte's digits to the rest of
its run: quadratic in the run's length, #1071). -/
def printDataItemsTR (l : List DataItem) : List String := go l "" #[]
where
  go : List DataItem → String → Array String → List String
    | [], run, out => (if run.isEmpty then out else out.push run).toList
    | .addr n off :: is, run, out =>
      go is "" ((if run.isEmpty then out else out.push run).push (addrToken n off))
    | .byte b :: is, run, out => go is (run ++ hexByte b) out

/-- A run `r` of bytes' digits before the tokens `ts` (`printDataItems`' `.byte` case for one byte). -/
private def glue (r : String) (ts : List String) : List String :=
  if r.isEmpty then ts else match ts with
    | t :: ts => if t.startsWith "%" then r :: t :: ts else (r ++ t) :: ts
    | [] => [r]

private theorem hexByte_startsWith (b : BitVec 8) (s : String) :
    (hexByte b ++ s).startsWith "%" = false := by
  have hm : ∀ c ∈ (['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f'] : List Char),
      c ≠ '%' := by decide
  have hd : ∀ n : Nat, (['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f'] : List Char)[n]?.getD '0' ≠ '%' := by
    intro n
    rcases h : (['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f'] : List Char)[n]? with _ | c
    · decide
    · exact hm c (List.mem_of_getElem? h)
  simp [hexByte, String.toList_append]
  exact fun h => hd _ h.symm

private theorem hexByte_ne (b : BitVec 8) (s : String) : (s ++ hexByte b).isEmpty = false := by
  rw [String.isEmpty_eq_false_iff]
  intro h
  have := congrArg String.toList h
  simp [hexByte, String.toList_append] at this

private theorem addrToken_startsWith (n : String) (off : Int) : (addrToken n off).startsWith "%" = true := by
  have : (toString "%" : String) = "%" := rfl
  simp [addrToken, String.toList_append, this]

private theorem glue_byte (r : String) (b : BitVec 8) (ts : List String) :
    glue (r ++ hexByte b) ts = glue r (glue (hexByte b) ts) := by
  have h1 : (hexByte b).isEmpty = false := by simpa using hexByte_ne b ""
  by_cases hr : r.isEmpty
  · have : r = "" := String.isEmpty_iff.1 hr
    subst this
    simp [glue]
  · have h2 : (r ++ hexByte b).isEmpty = false := hexByte_ne b r
    have hs := hexByte_startsWith b ""
    simp only [String.append_empty] at hs
    cases ts with
    | nil => simp [glue, hr, h1, h2, hs]
    | cons t ts =>
      by_cases ht : t.startsWith "%" = true
      · simp [glue, hr, h1, h2, hs, ht]
      · simp [glue, hr, h1, h2, hexByte_startsWith, ht, String.append_assoc]

private theorem printDataItems_byte (b : BitVec 8) (is : List DataItem) :
    printDataItems (.byte b :: is) = glue (hexByte b) (printDataItems is) := by
  have h1 : (hexByte b).isEmpty = false := by simpa using hexByte_ne b ""
  simp only [printDataItems, glue, h1]
  cases printDataItems is <;> rfl

private theorem printDataItemsTR_go : ∀ (l : List DataItem) (run : String) (out : Array String),
    printDataItemsTR.go l run out = out.toList ++ glue run (printDataItems l)
  | [], run, out => by
    by_cases hr : run.isEmpty <;> simp [printDataItemsTR.go, printDataItems, glue, hr]
  | .addr n off :: is, run, out => by
    rw [printDataItemsTR.go, printDataItemsTR_go is]
    have ht := addrToken_startsWith n off
    have hp : printDataItems (.addr n off :: is) = addrToken n off :: printDataItems is := rfl
    by_cases hr : run.isEmpty <;> simp [hp, glue, hr, ht]
  | .byte b :: is, run, out => by
    rw [printDataItemsTR.go, printDataItemsTR_go is, printDataItems_byte, glue_byte]

@[csimp] theorem printDataItems_eq_TR : @printDataItems = @printDataItemsTR := by
  funext l
  simp [printDataItemsTR, printDataItemsTR_go, glue]

/-- A `; data:` directive. -/
def dataObject (o : DataObject) : String :=
  s!"; data: %{o.name} align={o.align}{if o.writable then " writable" else ""} =" ++
    String.join ((printDataItems o.items).map (" " ++ ·))

def print (p : Program) : String :=
  let hdr := if p.header.isEmpty then "" else String.join (p.header.map (· ++ "\n")) ++ "\n"
  let hdr := hdr ++ String.join (p.data.map (dataObject · ++ "\n"))
  hdr ++ "\n".intercalate (p.funcs.map Function.print)

end Clif
