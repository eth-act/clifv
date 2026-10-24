import FV.E2E.StockProductionFixtures

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

end E2E.StockNarrowNIWitness
