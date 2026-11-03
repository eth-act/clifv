import FV.Backend.Lowering.Stock

/-!
# Native `i128` lowering for the stock driver (unverified)

`Opt.Legalize128` splits every `i128` value into two `i64` values before the lowering. Stock
Cranelift keeps an `i128` value in a register pair instead (`ValueRegs` with two vregs,
`machinst/vcode.rs` `VRegAllocator::alloc`) and lowers it with its own ISLE rules. This module
is that native route for a small foundation scope:

* `i128` block parameters, branch arguments, function parameters and returns;
* `isplit`, `iconcat`, `uextend`/`sextend` to `i128`, `ireduce` from `i128`, `bitcast.i128`;
* `brif` on an `i128` value (`orr` of the two halves, then `cbnz`);
* `ishl`, `ushr`, `sshr`, `rotl`, `rotr` of an `i128` value (`lower.isle` `lower_shl128`,
  `lower_ushr128`, `lower_sshr128` and the `rotl`/`rotr` `$I128` rules), and these shifts and
  rotates of a narrower value by an `i128` amount (the narrow rules use the amount's low
  register, `value_regs_get y 0`). These rules need no new extern: the externs `value_regs`
  and `value_regs_get` are `Backend.externCtor`'s, and the helpers (`lsl`, `orr_not`,
  `tst_imm`, `csel`, `imm`, `with_flags`, `consumes_flags_concat`) are ISLE rules;
* `icmp` of two `i128` values (`inst.isle` `emit_icmp_i128`): `cmp` of the low halves, then
  `ccmp` of the high halves for `eq`/`ne` (`emit_icmp_i128_eq_ne`) or `sbcs` for an ordering
  (the operands swapped for a greater-than or less-or-equal ordering). The flags feed the
  user of the `icmp` as for an `i64` `icmp`: a `cset`, the `b.cond` of a `brif`, the `csel`
  of a `select` (`is_nonzero_cmp`). No new extern either: `nzcv` is `Backend.externCtor`'s,
  and `ccmp`, `sbcs_side_effect`, `produces_flags_concat` are ISLE rules;
* `select` and `select_spectre_guard` of `i128` values (`lower_select_cond` at `$I128`): the
  flags of the condition (`is_nonzero_cmp`), then one `csel` per half; and a `select` of
  narrower values on an `i128` condition (`is_nonzero` at `$I128`: `orr` of the halves, then
  the `cmp` of `lower_select`). `select_spectre_guard` is lowered without `use_csdb`
  (`maybe_csdb_after_select` adds no `csdb`); the stock-configured driver rejects it under
  `use_csdb=true` (`StockConfig.usesCsdb`);
* `bmask` of an `i128` value or to `i128` (`lower_bmask`): `orr` of the halves, then `cmp` and
  `csetm`; the `csetm` register is both halves of an `i128` result;
* `bitselect` at `i128` (`bitselect_i128`): `and`, `bic` and `orr` of each half. The only new
  extern of these three items is `use_csdb` (false). Their helpers (`with_flags` of the two
  `CSel` of `ConsumesFlagsTwiceReturnsValueRegs`, `with_flags_reg`, `csetm`, `cmp_imm`,
  `and_imm`, `and_reg`, `bic`, `orr`) are ISLE rules, and `temp_writable_reg`, `value_reg`,
  `value_regs` and `value_regs_get` are `Backend.externCtor`'s.

Any other instruction with an `i128` operand or result makes `lower128` fail, so that a caller
can keep the legalized lowering. `FVTest.Backend.I128Native` routes the functions that
`lower128` lowers in the stock-configured driver. Nothing proves `lower128`.

`lower128` is a copy of `Stock.lower`, because `Stock.runTerm` is fixed to `Stock.sem`. The
copies of result binding, opportunistic definitions, branch arguments and block assembly use
all registers of a value. `Ctx.valReg` holds the low register of an `i128` value, and the side
table `HiRegs` holds its high register. On a function without `i128` values, every copied step
does what the original does (`FVTest.Backend.Lowering.StockI128Test` checks this
differentially).
-/

namespace Backend.Stock

open Isle Isle.Aarch64

/-- The high register of each `i128` value (index: value number). `Ctx.valReg` holds the low
register. Every other value has `none`. -/
abbrev HiRegs := Array (Option Reg)

def hiReg? (hi : HiRegs) (v : Nat) : Option Reg := (hi[v]?).join

/-- All registers of value `v` (Cranelift `value_regs[v]`): its low register, then its high
register if it is an `i128` value. -/
def valueRegs128? (ctx : Ctx) (hi : HiRegs) (v : Nat) : Option (List Reg) :=
  (ctx.valueReg? v).map fun lo => lo :: (hiReg? hi v).toList

/-! ## Instruction data and scope -/

/-- The shifts and rotates that `lower128` lowers with an `i128` operand: at `i128` (the
`$I128` rules of `lower.isle`), and at a narrower type by an `i128` amount. -/
def shift128 : Clif.BinaryOp → Bool
  | .ishl | .ushr | .sshr | .rotl | .rotr => true
  | _ => false

/-- `InstructionData` with the `i128` forms of the foundation: `isplit` of an `i128`,
`iconcat` of two `i64`, an extension to `i128`, `bitcast.i128`, an `i128` shift or rotate
(`shift128`), an `icmp` of two `i128` values (`IntCompare`), `select`,
`select_spectre_guard` and `bitselect` at `i128` (`Ternary`), `bmask` to `i128` (`Unary`).
Every other instruction is `instData` (which accepts `ireduce` from `i128`, a narrow shift by
an `i128` amount, a narrow `select` on an `i128` condition and a narrow `bmask` of an `i128`
value, because it checks the result type). -/
def instData128 (f : Clif.Function) : Clif.Inst → Except String V
  | .isplit .i128 x => pure (instDataV "Unary" [opcodeV "Isplit", .value x])
  | .binary op .i128 x y =>
    match shift128 op, binaryOpcode op with
    | true, some n => pure (instDataV "Binary" [opcodeV n, .values [x, y]])
    | _, _ => instData f (.binary op .i128 x y)
  | .iconcat .i64 x y => pure (instDataV "Binary" [opcodeV "Iconcat", .values [x, y]])
  | .extend op .i128 x =>
    pure (instDataV "Unary" [opcodeV (if op == .uextend then "Uextend" else "Sextend"), .value x])
  | .bitcast .i128 flags x =>
    pure (instDataV "LoadNoOffset" [opcodeV "Bitcast", .value x, .op (.memFlags flags)])
  | .icmp cc .i128 x y =>
    pure (instDataV "IntCompare" [opcodeV "Icmp", .values [x, y], mkVariant tyIntCC (intccName cc)])
  | .select .i128 c x y => pure (instDataV "Ternary" [opcodeV "Select", .values [c, x, y]])
  | .selectSpectreGuard .i128 c x y =>
    pure (instDataV "Ternary" [opcodeV "SelectSpectreGuard", .values [c, x, y]])
  | .bitselect .i128 c x y => pure (instDataV "Ternary" [opcodeV "Bitselect", .values [c, x, y]])
  | .bmask .i128 x => pure (instDataV "Unary" [opcodeV "Bmask", .value x])
  | i => instData f i

/-- The instructions of the foundation that may have an `i128` operand or result (`wide`: the
`i128` values). A shift or rotate (`shift128`) is in it at `i128`, and at a narrower type when
only its amount is an `i128` value. An `icmp` is in it at `i128`. A `select` is in it at `i128`
and on an `i128` condition, `select_spectre_guard` and `bitselect` at `i128`, and `bmask` at
`i128` and of an `i128` value. -/
def foundation128 (wide : Nat → Bool) : Clif.Inst → Bool
  | .isplit .i128 _ | .iconcat .i64 _ _ | .extend _ .i128 _ | .icmp _ .i128 _ _ => true
  | .selectSpectreGuard .i128 .. | .bitselect .i128 .. => true
  | .select ty c _ _ => ty == .i128 || wide c
  | .bmask ty x => ty == .i128 || wide x
  | .ireduce _ x | .bitcast .i128 _ x => wide x
  | .binary op ty x _ => shift128 op && (ty == .i128 || !wide x)
  | _ => false

/-- The terminators that may have an `i128` operand: branches and `return`. The calls of
`try_call`/`try_call_indirect`/`return_call` may not. -/
def termFoundation128 : Clif.Terminator → Bool
  | .tryCall .. | .tryCallIndirect .. | .returnCall .. => false
  | _ => true

/-! ## ABI (`isa/aarch64/abi.rs` `compute_arg_locs`, cranelift-codegen 0.136.1)

An `i128` parameter takes two X registers. The low half goes in an even register `x(2k)`, the
high half in `x(2k+1)`: an odd next register is skipped (AAPCS64 stage C.8, `abi.rs:293-337`).
When fewer than two X registers remain, the pair goes to a 16-byte aligned stack slot (low half
first), and the X registers stay available: a later `i64` parameter can still take `x7`. -/

/-- The locations of the parameters of `s`, one list per parameter (two entries for an `i128`),
each with the byte size of its load, and the stack-argument size. Without an `i128` parameter
this is `sigArgLocs` with the `sigParamBytes` sizes. -/
def sigArgLocs128 (s : Clif.Signature) : Except String (List (List (ArgLoc × Nat)) × Nat) := do
  if !s.params.any (·.ty == .i128) then
    let bytes ← sigParamBytes s
    let (locs, n) ← sigArgLocs s
    return ((locs.zip bytes).map fun (l, b) => [(l, b)], n)
  let mut locs : Array (List (ArgLoc × Nat)) := #[]
  let mut nx := 0
  let mut nv := 0
  let mut stack := 0
  for p in s.params do
    match p.purpose with
    | .sret =>
      if p.ty != .i64 then throw "sret parameter must be i64"
      locs := locs.push [(.reg (.x 8), 8)]
    | .normal | .vmctx =>
      if p.ty == .i128 then
        if nx + 2 ≤ 8 then
          let n := nx + nx % 2
          locs := locs.push [(.reg (.x n), 8), (.reg (.x (n + 1)), 8)]
          nx := n + 2
        else
          let off := alignTo stack 16
          locs := locs.push [(.stack off, 8), (.stack (off + 8), 8)]
          stack := off + 16
      else
        let bytes := p.ty.bytes
        let size := max bytes 8
        if p.ty.isInt && nx < 8 then
          locs := locs.push [(.reg (.x nx), bytes)]
          nx := nx + 1
        else if !p.ty.isInt && nv < 8 then
          locs := locs.push [(.reg (.v nv), bytes)]
          nv := nv + 1
        else
          let off := alignTo stack size
          locs := locs.push [(.stack off, bytes)]
          stack := off + size
    | _ => throw "special-purpose parameter (sarg)"
  pure (locs.toList, alignTo stack 16)

/-- The return registers of `s`, one list per ABI return (two for an `i128`, an even-aligned X
pair as for the parameters). Without an `i128` return these are the registers of
`Stock.externCtor`'s `gen_return`: x8 for the struct pointer of an `sret` signature, otherwise
`retRegs`. More returns than registers is an error (Cranelift's error without
`enable_multi_ret_implicit_sret`). -/
def retLocs128 (s : Clif.Signature) : Except String (List (List Reg)) := do
  if !s.returns.any (·.ty == .i128) then
    if (sigRets s).any (·.purpose == .sret) then return [[.x 8]]
    match retRegs (sigRets s).length with
    | some ps => return ps.map ([·])
    | none => throw "more than 8 return values"
  let mut out : Array (List Reg) := #[]
  let mut nx := 0
  let mut nv := 0
  for p in s.returns do
    if p.ty == .i128 then
      if nx + 2 ≤ 8 then
        let n := nx + nx % 2
        out := out.push [.x n, .x (n + 1)]
        nx := n + 2
      else throw "i128 return value without a free register pair"
    else if p.ty.isInt then
      if nx < 8 then
        out := out.push [.x nx]
        nx := nx + 1
      else throw "more than 8 return values"
    else if nv < 8 then
      out := out.push [.v nv]
      nv := nv + 1
    else throw "more than 8 float return values"
  pure out.toList

/-- Does the signature have an `i128` parameter or return? -/
def sigHas128 (s : Clif.Signature) : Bool :=
  s.params.any (·.ty == .i128) || s.returns.any (·.ty == .i128)

/-! ## Context and register allocation -/

/-- One allocation request: as `Allocation.step`, but an `i128` value takes two consecutive
integer vregs, low then high (`VRegAllocator::alloc`, `vcode.rs:1736-1738`). -/
def allocate128Step (valTy : Array (Option CTy)) (q : Allocation × HiRegs) :
    AllocationRequest → Allocation × HiRegs
  | .value x =>
    if (valTy[x]?).join == some (.int 128) then
      let (lo, base) := q.1.base.fresh .int
      let (h, base) := base.fresh .int
      ({ q.1 with valReg := q.1.valReg.set! x (some lo), base }, q.2.set! x (some h))
    else (q.1.step (.value x), q.2)
  | r => (q.1.step r, q.2)

/-- `allocateRequests` with register pairs for the `i128` values. -/
def allocate128 (valTy : Array (Option CTy)) (instructions : Nat)
    (requests : List AllocationRequest) : Allocation × HiRegs :=
  requests.foldl (allocate128Step valTy)
    (Allocation.initial valTy.size instructions, Array.replicate valTy.size none)

/-- `Stock.buildCtx` (with the body of `Backend.buildCtx`) that accepts `i128` values in the
foundation scope (`foundation128`, `termFoundation128`) and allocates a register pair to each
of them (`allocate128`). -/
def buildCtx128 (f : Clif.Function) :
    Except String (Ctx × Array (Nat × Nat) × State × HiRegs) := do
  let sigOf (r : Nat) : Option Clif.Signature := (f.extern? r).map (·.sig)
  let tyOk (ty : Clif.Ty) : Bool := valTyOk ty || ty == .i128
  let mut maxV := 0
  for b in f.blocks do
    for (v, _) in b.params do maxV := max maxV (v + 1)
    for s in b.body do
      for r in s.results do maxV := max maxV (r + 1)
  let mut valTy : Array (Option CTy) := Array.replicate maxV none
  let mut valDef : Array (Option Nat) := Array.replicate maxV none
  let mut insts : Array IInfo := #[]
  let mut ranges : Array (Nat × Nat) := #[]
  for b in f.blocks do
    for (v, ty) in b.params do
      if !tyOk ty then throw s!"block parameter v{v} is {ty.name}"
      valTy := valTy.set! v (some (CTy.ofClif ty))
    let start := insts.size
    for s in b.body do
      let data ← instData128 f s.inst
      let some tys := s.inst.resultTypes sigOf (f.sigDecls.lookup ·) |
        throw "ill-typed instruction"
      if tys.length != s.results.length then throw "result count mismatch"
      for (r, ty) in s.results.zip tys do
        if !tyOk ty then throw s!"value v{r} is {ty.name}"
        valTy := valTy.set! r (some (CTy.ofClif ty))
        valDef := valDef.set! r (some insts.size)
      insts := insts.push ⟨data, s.results, tys.map CTy.ofClif, some s.inst⟩
    insts := insts.push ⟨.op .unit, [], [], none⟩
    ranges := ranges.push (start, insts.size)
  for info in insts do
    let addr? : Option Nat := match info.clif with
      | some (.load _ _ _ p _) | some (.store _ _ _ _ p _) => some p
      | _ => none
    if let some p := addr? then
      if (valTy[p]?).join != some (.int 64) then
        throw s!"`{instText info.clif.get!}`: address v{p} is not i64 (pointer width 64)"
  -- the foundation scope: every other instruction with an `i128` operand or result fails
  let wide (v : Nat) : Bool := (valTy[v]?).join == some (.int 128)
  for b in f.blocks do
    for s in b.body do
      if ((instArgs s.inst).any wide || s.results.any wide) && !foundation128 wide s.inst then
        throw s!"`{instText s.inst}`: i128 instruction outside the native foundation"
    if (termArgs b.term).any wide && !termFoundation128 b.term then
      throw "i128 operand of a call terminator"
  if valTy.toList.any (fun o => o.any (·.valClass != .int)) then throw "f32/f64 value"
  let valReg : Array (Option Reg) := (Array.range maxV).map fun v =>
    ((valTy[v]?).join).map fun t => .vreg v t.valClass
  let (slotOff, _) := slotLayout f.slots
  let ctx : Ctx := { func := f, insts, valTy, valDef, valReg, slotOff }
  let requests ← allocationRequests f ranges
  let (allocation, hi) := allocate128 ctx.valTy ctx.insts.size requests
  let (ctx, ranges', st) := finishCtx ctx ranges allocation
  pure (ctx, ranges', st, hi)

/-! ## Extern constructors -/

/-- `Stock.externCtor` with register pairs. `put_in_regs` and `put_in_regs_vec` of an `i128`
value give both registers, with the demand and sunk-instruction checks of `Stock.externCtor`;
`output_pair` (`machinst/isle.rs`) makes a two-value output; `gen_return` of a signature with
an `i128` return places the registers at `retLocs128`; `use_csdb` is false (the stock setting
`use_csdb=false`; the stock-configured driver rejects `select_spectre_guard` under
`use_csdb=true`). `put_in_reg` of an `i128` value and calls with `i128` arguments or returns
are unmodeled. Everything else is `Stock.externCtor`. -/
def externCtor128 (ctx : Ctx) (hi : HiRegs) (t : Term) (args : List V) (st : State) :
    ExtResult (V × State) :=
  let wide (v : Nat) : Bool := (hiReg? hi v).isSome
  let sunk (v : Nat) : Bool := (ctx.defInst? v).any (fun i => st.sunk[i]!)
  match t.id, args with
  | TId.put_in_reg, [.value v] =>
    if wide v then .unmodeled s!"put_in_reg of the i128 value v{v}"
    else externCtor ctx t args st
  | TId.put_in_regs, [.value v] =>
    if wide v then
      if sunk v then .unmodeled s!"demand for sunk instruction of v{v}"
      else match valueRegs128? ctx hi v with
        | some rs => .ok (.regs rs, st.mark v)
        | none => .unmodeled s!"put_in_regs v{v}"
    else externCtor ctx t args st
  | TId.put_in_regs_vec, [.values vs] =>
    if vs.any wide then
      if vs.any sunk then .unmodeled "demand for sunk instruction"
      else match vs.mapM (valueRegs128? ctx hi) with
        | some rss => .ok (.regsVec rss, vs.foldl State.mark st)
        | none => .unmodeled "put_in_regs_vec"
    else externCtor ctx t args st
  | TId.output_pair, [.regs a, .regs b] => .ok (.regsVec [a, b], st)
  | TId.use_csdb, [] => .ok (.bool false, st)
  | TId.gen_return, [.regsVec rss] =>
    if ctx.func.sig.returns.any (·.ty == .i128) then
      match retLocs128 ctx.func.sig with
      | .error e => .unmodeled e
      | .ok ps =>
        if ps.length == rss.length && (ps.zip rss).all (fun (p, r) => p.length == r.length) then
          .ok (.op .unit, { st with base := st.base.emit (.rets (rss.flatten.zip ps.flatten)) })
        else .unmodeled "gen_return register count"
    else externCtor ctx t args st
  | TId.gen_call_output, [.op (.sig s)] | TId.gen_try_call_rets, [.op (.sig s)] =>
    if sigHas128 s then .unmodeled "call with an i128 parameter or return"
    else externCtor ctx t args st
  | TId.gen_call_rets, [.op (.sig s), _] =>
    if sigHas128 s then .unmodeled "call with an i128 parameter or return"
    else externCtor ctx t args st
  | TId.gen_call_args, [_, .regsVec rss] =>
    if rss.any (·.length != 1) then .unmodeled "call with an i128 argument"
    else externCtor ctx t args st
  | _, _ => externCtor ctx t args st

def sem128 (ctx : Ctx) (hi : HiRegs) : Isle.Sem V State :=
  { sem ctx with ctor := externCtor128 ctx hi }

def runTerm128 (ctx : Ctx) (hi : HiRegs) (term : String) (args : List V) (st : State) :
    Except String (Option V × State × List RuleId) :=
  match Isle.Interp.run program (sem128 ctx hi) {} term args st with
  | .ok r => .ok (r.value, r.state, r.trace)
  | .error e => .error s!"ISLE {term}: {repr e}"

/-! ## The driver (`Stock.lower` with register pairs) -/

/-- `bindResults` for all registers of each result: each register of the value gets an alias
of the corresponding output register (`lower.rs` `set_vreg_alias` per register), or a copy for
a physical output register. -/
def bindResults128 (ctx : Ctx) (hi : HiRegs) (pairs : List (Nat × List Reg)) (next : State) :
    Except String (State × Array MInst) :=
  pairs.foldlM (fun (st, extra) (v, rs) => do
    let some dsts := valueRegs128? ctx hi v | throw s!"unknown value v{v}"
    if dsts.length != rs.length then throw "multi-register result"
    (dsts.zip rs).foldlM (fun (st, extra) (vr, r) =>
      match r with
      | .vreg .. => return (← st.setAlias vr r, extra)
      | _ => return (st, extra.push (.mov .size64 vr r))) (st, extra)) (next, #[])

def emitInstruction128 (ctx : Ctx) (hi : HiRegs) (i : Nat) (before : State) :
    Except String Emission := do
  let info := ctx.insts[i]!
  let (out, next, fired) ← runTerm128 ctx hi "lower" [.inst i] before
  let some (.regsVec rss) := out | throw s!"no lowering rule for instruction {i}"
  if rss.length != info.results.length && !info.results.isEmpty then
    throw "lowering produced a wrong number of results"
  let (st, extra) ← bindResults128 ctx hi (info.results.zip rss) next
  pure ⟨st, st.base.emitted ++ extra, rss, fired⟩

/-- `commitOpportunisticValues` for all registers of each value (`try_use_opportunistic_defs`
aliases each register of the value). -/
def commitOpportunisticValues128 (ctx : Ctx) (hi : HiRegs) (values : List Nat) (st : State) :
    Except String State :=
  values.foldlM (fun s v => do
    if let some o := s.opportunistic[v]! then
      let some dsts := valueRegs128? ctx hi v | throw s!"unknown v{v}"
      if dsts.length != o.regs.length then throw "multi-register opportunistic definition"
      let next ← (dsts.zip o.regs).foldlM (fun s (dst, src) => s.setAlias dst src) s
      pure { next with opportunistic := next.opportunistic.set! v none }
    else pure s) st

def commitOpportunistic128 (ctx : Ctx) (hi : HiRegs) (block inst : Nat) (st : State) :
    Except String (Option State) := do
  let values := ctx.insts[inst]!.results
  if !values.all (fun v => st.demand[v]! == 0 ||
      (st.opportunistic[v]!).any (fun o => o.block == block && o.count == st.demand[v]!)) then
    return none
  return some (← commitOpportunisticValues128 ctx hi values st)

/-- `branchArgs` with all registers of each value argument (`collect_block_call`). -/
def branchArgs128 (ctx : Ctx) (hi : HiRegs) (st : State) (block index : Nat) :
    Except String (Array Reg × State) := do
  let b := ctx.func.blocks[block]!
  let some (id, args) := (destinations b.term)[index]? | throw "missing successor"
  let some target := ctx.func.block? id | throw s!"unknown block{id}"
  if args.length != target.params.length then throw s!"block{id}: argument count"
  let ti := (st.instBlock.findIdx? (· == block)).getD 0 + b.body.length
  let (rets, pays) := st.tryRegs[ti]!
  let nh := match b.term with
    | .tryCall _ _ et | .tryCallIndirect _ _ et => et.handlers.length
    | _ => 0
  let mut s := st
  let mut regs := #[]
  for a in args do
    match a with
    | .val v =>
      let some rs := valueRegs128? ctx hi v | throw s!"unknown value v{v}"
      s := s.mark v
      regs := regs ++ rs.toArray
    | .ret i =>
      if index < nh then throw "try_call return on exception edge"
      let some r := rets[i]? | throw "try_call return index"
      regs := regs.push r
    | .exn i =>
      if index == nh then throw "try_call payload on normal edge"
      let some r := pays[i]? | throw "try_call payload index"
      regs := regs.push r
  pure (regs, s)

def scanInstruction128 (ctx : Ctx) (hi : HiRegs) (block i ti : Nat) (isBranch : Bool)
    (input : State) : Except String Scan := do
  if input.sunk[i]! then
    return ⟨input, some ⟨block, i, .sunk, input, input, [], [], #[]⟩, #[]⟩
  let before := scanState input i
  if i == ti && isBranch then return ⟨before, none, #[]⟩
  let info := ctx.insts[i]!
  let mandatory := if i == ti then true else info.clif.any mustLower
  if !mandatory && !info.results.any (fun v => before.demand[v]! != 0) then
    return ⟨before, some ⟨block, i, .omitted, before, before, [], [], #[]⟩, #[]⟩
  if before.entryColor[i]! == 0 && !mandatory then
    if let some next ← commitOpportunistic128 ctx hi block i before then
      return ⟨next, some ⟨block, i, .opportunistic, before, next, [], [], #[]⟩, #[]⟩
  let emission ← emitInstruction128 ctx hi i before
  pure (emission.scan block i before)

def scanBlock128 (ctx : Ctx) (hi : HiRegs) (block ti : Nat) (isBranch : Bool)
    (indices : List Nat) (input : State) : Except String BlockScan :=
  runScans (fun i => scanInstruction128 ctx hi block i ti isBranch) indices input

def outgoingStep128 (ctx : Ctx) (hi : HiRegs) (order : Order) (bi : Nat)
    (acc : State × Array (Array Reg)) (target : Nat × Nat) :
    Except String (State × Array (Array Reg)) := do
  match order.nodes[target.1]! with
  | .edge .. => pure (acc.1, acc.2.push #[])
  | _ =>
    let (args, next) ← branchArgs128 ctx hi acc.1 bi target.2
    pure (next, acc.2.push args)

def collectOutgoing128 (ctx : Ctx) (hi : HiRegs) (order : Order) (bi : Nat)
    (targets : Array Nat) (input : State) : Except String (State × Array (Array Reg)) :=
  targets.zipIdx.toList.foldlM (outgoingStep128 ctx hi order bi) (input, #[])

def emitBranch128 (ctx : Ctx) (hi : HiRegs) (f : Clif.Function) (t : Clif.Terminator)
    (bi ti : Nat) (targets : Array Nat) (input : State) : Except String BranchEmission := do
  let before := { input with current := some ti, color := none, base.emitted := #[] }
  let (out, next, fired) ← runTerm128 ctx hi "lower_branch" [.inst ti, .labels targets.toList] before
  if out.isNone then throw s!"no lowering rule for terminator {repr t}"
  let code ← branchCode f t targets next.base.emitted
  pure ⟨next, code, ⟨bi, ti, .emitted, before, next, [], fired, code⟩, fired⟩

def lowerBlockCore128 (ctx : Ctx) (hi : HiRegs) (order : Order) (f : Clif.Function)
    (b : Clif.Block) (bi start stop : Nat) (data : V) (targets : Array Nat)
    (input : State) : Except String LoweredBlockCore := do
  let ti := stop - 1
  let termCtx := { ctx with
    insts := ctx.insts.set! ti ⟨data, [], [], none⟩
    tryRegs := input.tryRegs[ti]! }
  let isBranch := match b.term with | .ret .. | .trap .. | .returnCall .. => false | _ => true
  let branch ← if isBranch then
    some <$> emitBranch128 termCtx hi f b.term bi ti targets input else pure none
  let beforeEdges := branch.map (·.state) |>.getD input
  let (next, outgoing) ← collectOutgoing128 ctx hi order bi targets beforeEdges
  let beforeScan := { next with color := some next.endColor[bi]! }
  let indices := ((Array.range (stop - start)).map (start + ·)).reverse.toList
  let bodyScan ← scanBlock128 termCtx hi bi ti isBranch indices beforeScan
  pure ⟨bodyScan.state, bodyScan.code ++ (branch.map (·.code) |>.getD #[]), outgoing,
    branch, ⟨termCtx, bi, ti, isBranch, indices, beforeScan, bodyScan⟩⟩

/-- `assembleOriginalBlock` with register pairs: an entry parameter gets one `args` pair or
stack load per location (`sigArgLocs128`, `gen_copy_arg_to_regs`), and a block parameter one
VCode parameter per register (`add_block_params`). -/
def assembleOriginalBlock128 (ctx : Ctx) (hi : HiRegs) (b : Clif.Block)
    (bi label : Nat) (targets : Array Nat) (outgoing : Array (Array Reg))
    (locs : List (List (ArgLoc × Nat))) (uses : Array UseState) (bodyCode : Array MInst) :
    Except String VBlock := do
  let mut code := bodyCode
  if bi == 0 then
    let mut pairs := []
    let mut loads := #[]
    for ((v, _), slots) in b.params.zip locs do
      if uses[v]! == .unused then continue
      let some rs := valueRegs128? ctx hi v | throw s!"unknown value v{v}"
      if rs.length != slots.length then throw s!"parameter v{v}: register count"
      for (r, (loc, bytes)) in rs.zip slots do
        match loc with
        | .reg p => pairs := pairs ++ [(r, p)]
        | .stack off =>
          loads := loads.push (.load (loadOpOfBytes bytes) r (.fpOffset (16 + off)) trustedFlags)
    if !pairs.isEmpty then code := #[.args pairs] ++ loads ++ code
    else code := loads ++ code
  let params ← if bi == 0 then pure #[] else do
    let rss ← b.params.toArray.mapM fun (v, _) =>
      match valueRegs128? ctx hi v with
      | some rs => pure rs.toArray
      | none => throw s!"unknown value v{v}"
    pure rss.flatten
  let args := if targets.size == 1 then outgoing[0]! else #[]
  pure { label, insts := code, params, branchArgs := args }

def lowerNode128 (ctx : Ctx) (hi : HiRegs) (ranges : Array (Nat × Nat)) (order : Order)
    (f : Clif.Function) (locs : List (List (ArgLoc × Nat))) (label : Nat) (input : DriverState) :
    Except String DriverState := do
  let targets := order.successors[label]!
  match order.nodes[label]! with
  | .edge pred k _ =>
    let (args, next) ← branchArgs128 ctx hi input.state pred k
    pure { input with
      state := next
      blocks := input.blocks.set! label { label, insts := #[.jump targets[0]!], branchArgs := args },
      edgeArgs := input.edgeArgs.set! label #[args] }
  | .original bi =>
    let b := f.blocks[bi]!
    let (start, stop) := ranges[bi]!
    let data ← match b.term with
      | .tryCall .. | .tryCallIndirect .. => tryCallData f b.term
      | _ => termData (abiTerm f b.term)
    if b.term matches .ret .. && (sretRet f).isEmpty && sigRets f.sig != f.sig.returns then
      throw "sret parameter is not an entry-block parameter"
    let lowered ← lowerBlockCore128 ctx hi order f b bi start stop data targets input.state
    let block ← assembleOriginalBlock128 ctx hi b bi label targets lowered.outgoing
      locs lowered.state.uses lowered.code
    pure { recordCore input lowered bi stop with
      blocks := input.blocks.set! label block,
      edgeArgs := input.edgeArgs.set! label lowered.outgoing }

/-- `lower128` with the high-register table of the `i128` values. -/
def lower128WithHi (f : Clif.Function) : Except String (Result × HiRegs) := do
  if !aapcsConv f.sig.callConv then throw s!"calling convention {repr f.sig.callConv}"
  let (locs, _) ← sigArgLocs128 f.sig
  if f.sig.params.any (·.purpose == .sret) && !f.sig.returns.isEmpty then
    throw "sret parameter together with return values"
  discard <| retLocs128 f.sig
  let (ctx, ranges, initial, hi) ← buildCtx128 f
  let order ← blockOrder f
  let driver0 : DriverState := {
    state := initial
    blocks := Array.replicate order.nodes.size default
    edgeArgs := Array.replicate order.nodes.size #[]
    schedule := #[], scans := #[], blockScans := #[], rules := #[] }
  let driver ← (Array.range order.nodes.size).reverse.toList.foldlM
    (fun input label => lowerNode128 ctx hi ranges order f locs label input) driver0
  let st := driver.state
  let mut blocks := driver.blocks
  let mut edgeArgs := driver.edgeArgs
  let resolve := Backend.lowerFunction.resolve st.alias (st.alias.size + 1)
  blocks := blocks.map fun b => { b with
    insts := b.insts.map (·.mapRegs resolve)
    params := b.params.map resolve
    branchArgs := b.branchArgs.map resolve }
  edgeArgs := edgeArgs.map fun args => args.map fun rs => rs.map resolve
  let (_, slotBytes) := slotLayout f.slots
  pure ({
    ctx := ctx
    initial := initial
    final := st
    order := order
    edgeArgs := edgeArgs
    schedule := driver.schedule
    scans := driver.scans
    blockScans := driver.blockScans
    code := { name := f.name, blocks, classes := st.base.classes,
              slotBytes, outgoing := st.base.outgoing, rulesFired := driver.rules } }, hi)

/-- **The native `i128` stock lowering** (foundation scope, unverified). `Stock.lower` with
`i128` values in register pairs; it fails on every `i128` instruction outside the foundation
(`foundation128`). -/
def lower128 (f : Clif.Function) : Except String Result :=
  (·.1) <$> lower128WithHi f

end Backend.Stock
