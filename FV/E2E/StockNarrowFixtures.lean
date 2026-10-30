import FV.Backend.Lowering.StockD0

namespace E2E.StockNarrowNIWitness
open Backend.Stock.D0
set_option autoImplicit false

structure Case where
  name : String
  inputTy : Clif.Ty
  inst : Clif.Inst

def widths : List Clif.Ty := [.i8,.i16]

def conventions : List Configuration := [.defaultI32,.systemVI32,.fastI32]

/-- Original source operations, including comparisons and cross-width casts. -/
def cases (ty : Clif.Ty) : List Case :=
  [⟨"constant",ty,.iconst ty (BitVec.ofNat ty.width 0xb5)⟩,
   ⟨"select",ty,.select ty 0 1 8⟩] ++
  ([.bnot,.ineg,.clz,.ctz,.bitrev,.bswap,.popcnt] : List Clif.UnaryOp).map
    (fun op => ⟨s!"unary_{repr op}",ty,.unary op ty 1⟩) ++
  ([.iadd,.isub,.band,.bor,.bxor,.imul,.ishl,.ushr,.sshr,.rotl,.rotr,
    .smin,.smax,.umin,.umax,.smulhi,.umulhi] : List Clif.BinaryOp).map
    (fun op => ⟨s!"binary_{repr op}",ty,.binary op ty 1 8⟩) ++
  ([.eq,.slt,.ult] : List Clif.IntCC).map
    (fun cc => ⟨s!"compare_{repr cc}",ty,.icmp cc ty 1 8⟩) ++
  ([.sdiv,.udiv,.srem,.urem] : List Clif.DivOp).map
    (fun op => ⟨s!"division_{repr op}",ty,.div op ty 1 8⟩) ++
  [⟨"reduce32",.i32,.ireduce ty 1⟩,⟨"reduce64",.i64,.ireduce ty 1⟩,
   ⟨"unsigned32",ty,.extend .uextend .i32 1⟩,⟨"signed32",ty,.extend .sextend .i32 1⟩,
   ⟨"unsigned64",ty,.extend .uextend .i64 1⟩,⟨"signed64",ty,.extend .sextend .i64 1⟩]

def resultType (c : Case) : Clif.Ty :=
  ((c.inst.resultTypes (fun _ => none) (fun _ => none)).getD []).headD c.inputTy

/-- Nine original arguments retain a real stack argument and explicit source slot. -/
def function (config : Configuration) (c : Case) : Clif.Function :=
  {source s!"stock_narrow_{c.inputTy.width}_{(resultType c).width}_{c.name}_{repr config}" config [] with
    sig := {
      params := List.replicate 9 ⟨c.inputTy,.none,.normal⟩
      returns := [⟨resultType c,.none,.normal⟩]
      callConv := convention config}
    slots := [(7,⟨8,some 8⟩)]
    blocks := [{
      id := 0
      params := (List.range 9).map fun i => (i,c.inputTy)
      body := [⟨[100],c.inst⟩]
      term := .ret [100]}]}

/-- Mixed-width casts, fused scalar users and a retained unused division. -/
def mixedBody (ty : Clif.Ty) : List Clif.Stmt :=
  [⟨[100],.iconst ty (BitVec.ofNat ty.width 0xb5)⟩,
   ⟨[101],.binary .iadd ty 1 100⟩,⟨[102],.binary .imul ty 101 8⟩,
   ⟨[103],.div .sdiv ty 102 8⟩,⟨[104],.icmp .ult ty 103 1⟩,
   ⟨[105],.select ty 104 103 1⟩,⟨[106],.extend .sextend .i64 105⟩,
   ⟨[107],.ireduce ty 106⟩,⟨[108],.unary .bnot ty 107⟩,
   ⟨[109],.binary .rotl ty 108 8⟩,⟨[110],.binary .umin ty 109 1⟩,
   ⟨[111],.unary .popcnt ty 110⟩,⟨[112],.binary .smulhi ty 111 8⟩,
   ⟨[113],.div .urem ty 112 8⟩,
   ⟨[114],.iconst ty (BitVec.ofNat ty.width 0xee)⟩]

def mixedFunction (config : Configuration) (ty : Clif.Ty) : Clif.Function :=
  let old := function config ⟨"mixed",ty,.unary .bnot ty 1⟩
  {old with blocks := old.blocks.map fun b => {b with body := mixedBody ty,term := .ret [112]}}

/-- This is a fixture classification only; production keeps its original scope check. -/
def outsideOriginalScope (c : Case) : Bool :=
  match c.inst with
  | .unary .bswap .i8 _ => true
  | _ => false

def arguments (ty : Clif.Ty) (input : Nat → BitVec ty.width) : List Clif.Val :=
  (List.range 9).map fun i => ⟨ty,input i⟩

def frame (f : Clif.Function) (ty : Clif.Ty) (input : Nat → BitVec ty.width)
    (slot : Nat) : Clif.Frame := {
  func := f
  regs := (Clif.Regs.empty.setMany (List.range 9) (arguments ty input)).getD Clif.Regs.empty
  slots := [(7,slot)]
  body := f.blocks[0]!.body
  term := f.blocks[0]!.term }

def caseInput (ty : Clif.Ty) (sample : Nat) : Nat → BitVec ty.width :=
  fun i => BitVec.ofNat ty.width
    (if sample == 0 then 0 else if sample == 1 then 2*i+1
     else if i == 1 then 2^(ty.width-1) else if i == 8 then 2^ty.width-1 else 2*i+1)

def sourceRun (f : Clif.Function) (ty : Clif.Ty) (sample : Nat) : Clif.Outcome :=
  Clif.runLoop Clif.Env.empty {funcs := []} (f.blocks[0]!.body.length+2)
    ⟨frame f ty (caseInput ty sample) 4096,[],Clif.Mem.empty⟩

end E2E.StockNarrowNIWitness
