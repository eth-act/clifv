import FV.E2E.StockPopcountFixtures
namespace E2E.StockMinMaxNIWitness
open Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false

def extraBody (config : Configuration) : List Clif.Stmt :=
  let ty := valueType config
  [⟨[201],.binary .smin ty 1 2⟩,⟨[202],.binary .smax ty 1 8⟩,
   ⟨[203],.binary .umin ty 2 3⟩,⟨[204],.binary .umax ty 0 8⟩,
   ⟨[205],.iconst ty (BitVec.ofNat ty.width 7)⟩,
   ⟨[206],.iconst ty (BitVec.ofNat ty.width 0x123456789abcdef)⟩,
   ⟨[240],.iconst ty (BitVec.ofInt ty.width (-7))⟩,
   ⟨[207],.binary .smin ty 1 205⟩,⟨[208],.binary .smax ty 2 240⟩,
   ⟨[209],.binary .umin ty 8 205⟩,⟨[210],.binary .umax ty 0 240⟩,
   ⟨[211],.binary .smin ty 206 1⟩,⟨[212],.binary .smax ty 206 2⟩,
   ⟨[213],.binary .umin ty 206 8⟩,⟨[214],.binary .umax ty 206 0⟩,
   ⟨[215],.binary .iadd ty 201 202⟩,⟨[216],.binary .bxor ty 215 203⟩,
   ⟨[217],.binary .iadd ty 216 204⟩,⟨[218],.binary .bxor ty 217 207⟩,
   ⟨[219],.binary .iadd ty 218 208⟩,⟨[220],.binary .bxor ty 219 209⟩,
   ⟨[221],.binary .iadd ty 220 210⟩,⟨[222],.binary .bxor ty 221 211⟩,
   ⟨[223],.binary .iadd ty 222 212⟩,⟨[224],.binary .bxor ty 223 213⟩,
   ⟨[225],.binary .iadd ty 224 214⟩,⟨[226],.binary .bxor ty 78 225⟩]

def function (config : Configuration) : Clif.Function :=
  let old := StockPopcountNIWitness.function config
  {old with name := "stock_minmax_ni", blocks := old.blocks.map fun b =>
    {b with body := b.body ++ extraBody config, term := .ret [226]}}

def resultValue (config : Configuration) (input : Nat → BitVec (valueType config).width) :
    BitVec (valueType config).width :=
  let small := BitVec.ofNat (valueType config).width 7
  let negative := BitVec.ofInt (valueType config).width (-7)
  let large := BitVec.ofNat (valueType config).width 0x123456789abcdef
  let a := Clif.Sem.binary .smin (input 1) (input 2)
  let b := Clif.Sem.binary .smax (input 1) (input 8)
  let c := Clif.Sem.binary .umin (input 2) (input 3)
  let d := Clif.Sem.binary .umax (input 0) (input 8)
  let e := Clif.Sem.binary .smin (input 1) small
  let f := Clif.Sem.binary .smax (input 2) negative
  let g := Clif.Sem.binary .umin (input 8) small
  let h := Clif.Sem.binary .umax (input 0) negative
  let i := Clif.Sem.binary .smin large (input 1)
  let j := Clif.Sem.binary .smax large (input 2)
  let k := Clif.Sem.binary .umin large (input 8)
  let l := Clif.Sem.binary .umax large (input 0)
  let mixed := ((((((((((a+b) ^^^ c)+d) ^^^ e)+f) ^^^ g)+h) ^^^ i)+j) ^^^ k)+l
  StockPopcountNIWitness.resultValue config input ^^^ mixed
end E2E.StockMinMaxNIWitness
