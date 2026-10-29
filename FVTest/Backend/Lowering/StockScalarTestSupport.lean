module

@[expose] public section

namespace FVTest.StockScalarFixture
/-- A two-block legacy control remains outside the current pure-body class as
new scalar opcodes are activated. It retains the native multiplication result. -/
def legacySource (name : String) : String :=
  "function %" ++ name ++ "(i64, i64) -> i64 {\nblock0(v0: i64, v1: i64):\n    v2 = imul v0, v1\n    jump block1(v2)\nblock1(v3: i64):\n    return v3\n}\n"
end FVTest.StockScalarFixture
