import FV.E2E.StockMinMaxFixtures
namespace E2E.StockCmpNIWitness
open Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false

/-- Every original integer condition, plus both zero sides, adjusted immediates
and nonencodable constants. Each result contributes distinct observable bits. -/
def comparisons : List (Clif.IntCC × Nat × Nat) :=
  [(.eq,1,2),(.ne,1,2),(.slt,1,2),(.sle,1,2),(.sgt,1,2),(.sge,1,2),
   (.ult,1,2),(.ule,1,2),(.ugt,1,2),(.uge,1,2),
   (.eq,1,301),(.ne,2,301),(.eq,301,1),(.ne,301,2),
   (.slt,1,205),(.ule,2,302),(.sge,1,303),(.ugt,2,302),(.slt,304,1),(.ult,304,2)]

def extraBody (config : Configuration) : List Clif.Stmt :=
  let ty := valueType config
  [⟨[301],.iconst ty (BitVec.ofNat ty.width 0)⟩,
   ⟨[302],.iconst ty (BitVec.ofNat ty.width 4097)⟩,
   ⟨[303],.iconst ty (BitVec.ofInt ty.width (-4097))⟩,
   ⟨[304],.iconst ty (BitVec.ofNat ty.width 0x123456789abcdef)⟩] ++
  comparisons.zipIdx.flatMap fun ((cc,x,y),k) =>
    let base := 1000+10*k
    let previous := if k = 0 then 226 else 1000+10*(k-1)+6
    [⟨[base],.icmp cc ty x y⟩,
     ⟨[base+1],.extend .uextend ty base⟩,
     ⟨[base+2],.extend .sextend ty base⟩,
     ⟨[base+3],.binary .imul ty (base+1) (base+2)⟩,
     ⟨[base+4],.iconst ty (BitVec.ofNat ty.width k)⟩,
     ⟨[base+5],.binary .ishl ty (base+3) (base+4)⟩,
     ⟨[base+6],.binary .bxor ty previous (base+5)⟩]

def function (config : Configuration) : Clif.Function :=
  let old := StockMinMaxNIWitness.function config
  {old with name := "stock_cmp_ni",blocks := old.blocks.map fun b =>
    {b with body := b.body ++ extraBody config,term := .ret [1196]}}

def resultValue (config : Configuration) (input : Nat → BitVec (valueType config).width) :
    BitVec (valueType config).width :=
  let width := (valueType config).width
  let read := fun key =>
    if key = 301 then BitVec.ofNat width 0
    else if key = 302 then BitVec.ofNat width 4097
    else if key = 303 then BitVec.ofInt width (-4097)
    else if key = 304 then BitVec.ofNat width 0x123456789abcdef
    else if key = 205 then BitVec.ofNat width 7
    else input key
  comparisons.zipIdx.foldl (fun acc ((cc,x,y),k) =>
    let b := Clif.Sem.icmp cc (read x) (read y)
    let doubled := Clif.Sem.binary .imul (Clif.Sem.uextend width b) (Clif.Sem.sextend width b)
    acc ^^^ Clif.Sem.binary .ishl doubled (BitVec.ofNat width k))
    (StockMinMaxNIWitness.resultValue config input)
end E2E.StockCmpNIWitness
