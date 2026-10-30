import FV.E2E.StockHighMulFixtures
namespace E2E.StockAluRootsWitness
open Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false

/-- A constant outside every imm12 form, so the extend roots keep a register operand. -/
def wide : Nat := 0x123456789abcdef

/-- Immediate, negated-immediate, shifted-operand and `bnot`-operand forms of
add/sub/and/or/xor, in the original value type. `extr` (roots 862/863) emits
`aluRRRShift .extr`, which `ABIReadScalar.bitProducer` does not admit, so it stays out. -/
def operandBody (config : Configuration) : List Clif.Stmt :=
  let ty := valueType config
  let w := ty.width
  [⟨[5001],.iconst ty 5⟩,⟨[5002],.binary .iadd ty 1 5001⟩,
   ⟨[5003],.iconst ty 9⟩,⟨[5004],.binary .iadd ty 5003 2⟩,
   ⟨[5005],.iconst ty (2^w - 5)⟩,⟨[5006],.binary .iadd ty 8 5005⟩,
   ⟨[5007],.iconst ty (2^w - 9)⟩,⟨[5008],.binary .iadd ty 5007 1⟩,
   ⟨[5015],.iconst ty 3⟩,⟨[5016],.binary .ishl ty 2 5015⟩,⟨[5017],.binary .iadd ty 1 5016⟩,
   ⟨[5018],.iconst ty 4⟩,⟨[5019],.binary .ishl ty 1 5018⟩,⟨[5020],.binary .iadd ty 5019 8⟩,
   ⟨[5021],.iconst ty 7⟩,⟨[5022],.binary .isub ty 2 5021⟩,
   ⟨[5023],.iconst ty (2^w - 7)⟩,⟨[5024],.binary .isub ty 8 5023⟩,
   ⟨[5028],.iconst ty 2⟩,⟨[5029],.binary .ishl ty 8 5028⟩,⟨[5030],.binary .isub ty 1 5029⟩,
   ⟨[5031],.unary .bnot ty 2⟩,⟨[5032],.binary .band ty 1 5031⟩,
   ⟨[5033],.unary .bnot ty 8⟩,⟨[5034],.binary .band ty 5033 2⟩,
   ⟨[5035],.unary .bnot ty 1⟩,⟨[5036],.binary .bor ty 8 5035⟩,
   ⟨[5037],.unary .bnot ty 2⟩,⟨[5038],.binary .bor ty 5037 1⟩,
   ⟨[5039],.unary .bnot ty 8⟩,⟨[5040],.binary .bxor ty 2 5039⟩]

/-- Extended-operand add/sub. The class admits only i32/i64 casts, so i32 configurations
extend into i64 arithmetic and reduce the result back. -/
def extendBody (config : Configuration) : List Clif.Stmt :=
  if valueType config == .i64 then
    [⟨[5009],.ireduce .i32 2⟩,⟨[5010],.extend .uextend .i64 5009⟩,
     ⟨[5011],.binary .iadd .i64 1 5010⟩,
     ⟨[5012],.ireduce .i32 8⟩,⟨[5013],.extend .sextend .i64 5012⟩,
     ⟨[5014],.binary .iadd .i64 5013 2⟩,
     ⟨[5025],.ireduce .i32 1⟩,⟨[5026],.extend .uextend .i64 5025⟩,
     ⟨[5027],.binary .isub .i64 2 5026⟩]
  else
    [⟨[5009],.iconst .i64 wide⟩,⟨[5010],.extend .uextend .i64 2⟩,
     ⟨[5049],.binary .iadd .i64 5009 5010⟩,⟨[5011],.ireduce .i32 5049⟩,
     ⟨[5013],.extend .sextend .i64 8⟩,
     ⟨[5050],.binary .iadd .i64 5013 5009⟩,⟨[5014],.ireduce .i32 5050⟩,
     ⟨[5026],.extend .uextend .i64 1⟩,
     ⟨[5051],.binary .isub .i64 5009 5026⟩,⟨[5027],.ireduce .i32 5051⟩]

/-- Keep every new result live in the returned value. -/
def combineBody (config : Configuration) : List Clif.Stmt :=
  let ty := valueType config
  [⟨[5101],.binary .bxor ty 4008 5002⟩,⟨[5102],.binary .bxor ty 5101 5004⟩,
   ⟨[5103],.binary .bxor ty 5102 5006⟩,⟨[5104],.binary .bxor ty 5103 5008⟩,
   ⟨[5105],.binary .bxor ty 5104 5011⟩,⟨[5106],.binary .bxor ty 5105 5014⟩,
   ⟨[5107],.binary .bxor ty 5106 5017⟩,⟨[5108],.binary .bxor ty 5107 5020⟩,
   ⟨[5109],.binary .bxor ty 5108 5022⟩,⟨[5110],.binary .bxor ty 5109 5024⟩,
   ⟨[5111],.binary .bxor ty 5110 5027⟩,⟨[5112],.binary .bxor ty 5111 5030⟩,
   ⟨[5113],.binary .bxor ty 5112 5032⟩,⟨[5114],.binary .bxor ty 5113 5034⟩,
   ⟨[5115],.binary .bxor ty 5114 5036⟩,⟨[5116],.binary .bxor ty 5115 5038⟩,
   ⟨[5117],.binary .bxor ty 5116 5040⟩]

def extraBody (config : Configuration) : List Clif.Stmt :=
  operandBody config ++ extendBody config ++ combineBody config

def function (config : Configuration) : Clif.Function :=
  let old := E2E.StockHighMulNIWitness.function config
  {old with name := "stock_alu_roots",blocks := old.blocks.map fun b =>
    {b with body := b.body ++ extraBody config,term := .ret [5117]}}
end E2E.StockAluRootsWitness
