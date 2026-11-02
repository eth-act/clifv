Actual pipeline checks now construct the register-aware program contract and the existing program statement. This connects the shared linker proofs to executable artifact validation.

- Share the existing metadata proof. Preserve all 38 other conditions and the three original producer statements and axiom sets.
- Extend only the lowering verdict. Retain every other check and the existing cached link context.
- Derive physical call compatibility inside the compilation field. Require no caller execution certificate.
- Validate the unchanged sret capture in both cleanup modes, including its original settings header. Its actual artifact selects the Stock ABI.
- Keep a real mixed-program rejection witness. Every old check passes, but its legacy caller expects the implicit result in x0 while the Stock callee returns it in x8.

Validation: the 2,958-module importer closure and 19 roots passed before the final main refresh. On current main through #851, the 1,727-module focused closure and all 20 roots pass. The three old statements and axiom sets remain exact. Generic correctness uses only standard axioms. Fixed witnesses retain annotated native dependencies.

No production selector changes. The mixed caller needs a proved adapter. Remaining consumers, complete-file fallback, cached physical checks, default activation, and original #140 remain open.
