import FV.Backend.Proof.IselPrgDriverT
import FV.E2E.LinkScopeT

/-!
Non-vacuity of the typed ISLE progress (`Prg.lowerFunction_ok_inputT`, S11 #35 slice 8): a
function of the typed scope with an `i64` parameter, an `f64` return, two `f64const`s from `2^32`
on (`2.0`: an `fmov d` immediate, rule 3 of `constant_f64`; `0x400921FB00000000`: zero low 32 bits,
not an `fmov` immediate, rule 1), one below `2^32` (`constant_f32`), and a float `select`
satisfies every premise (decided by `native_decide`, witness only; the bit-pattern routes and
the scope exclusion by the kernel), so `lowerFunction` succeeds on it by the
theorem, outside subset E (`Compile.functionE` fails). `lake build FVTest.Backend.FloatProgT`.
-/

open Backend Backend.Proof Backend.Proof.Driver

namespace FloatProgT

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- `f64const 2.0`, `f64const 0x400921FB00000000`, `f64const 0x1p-1060` (bits `1`), and a
`select` of floats on the parameter. -/
def fConstF64 : Clif.Function where
  name := "c64"
  sig := { params := [{ ty := .i64 }], returns := [{ ty := .f64 }] }
  blocks := [
    { id := 0, params := [(0, .i64)],
      body := [⟨[1], .iconst .f64 0x4000000000000000⟩, ⟨[2], .iconst .f64 0x400921FB00000000⟩,
        ⟨[3], .iconst .f64 1⟩, ⟨[4], .select .f64 0 1 2⟩, ⟨[5], .select .f64 0 4 3⟩],
      term := .ret [5] }]

/-- The bit patterns take the three pool-free routes of `constant_f64`. -/
theorem fConstF64_routes :
    (Backend.fpModImm? 0x4000000000000000 .size64).isSome = true ∧
      (Backend.fpModImm? 0x400921FB00000000 .size64).isSome = false ∧
      0x400921FB00000000 % 2 ^ 32 = 0 := by
  decide +kernel

/-- Outside subset E. -/
theorem fConstF64_not_E : Compile.functionE fConstF64 = false := by decide +kernel

/-- **Non-vacuity of `Prg.lowerFunction_ok_inputT`**: every premise holds on `fConstF64`. -/
theorem lowerFunction_ok_inputT_witness : ∃ vc, lowerFunction fConstF64 = .ok vc :=
  Prg.lowerFunction_ok_inputT (by native_decide) (by native_decide) (by native_decide)
    (E2E.LinkCheck.lowerScopeT_of (by native_decide)) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)

end FloatProgT
