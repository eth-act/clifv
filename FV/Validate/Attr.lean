/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license.
-/
import Lean

/-- Simp set of the validator's frame/relation lemmas (used by `vside`). -/
register_simp_attr vsimp

/-- CLIF per-opcode semantics unfolded before bit-blasting. -/
register_simp_attr vsem
