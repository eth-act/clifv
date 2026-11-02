# Stock call results with a live arithmetic parameter

This packet proves the complete function class for one direct call followed by addition.
The caller uses its original parameter after the call.
The callee can change memory and caller-saved registers.
The original function returns the call result plus the live parameter.

The source checker derives the retained value maps, final aliases, and actual instruction order.
The proofs compose the existing call-result binder, addition semantics, source semantics, and machine NI.
The provider selects the new Stock code before the complete supplied predecessor.
Every explicit predecessor route remains unchanged.
The packet takes no route index and changes no shared selector.

The complete witness uses source values 7, 31, and 79.
Its virtual registers are 192, 196, and 195 after alias resolution.
The real allocator saves the live parameter in x19 in both cleanup modes.
The callee changes x0 and returns the original argument plus 13.
The symbolic source execution returns (word + 13) + word.
The actual predecessor accepts this caller, and the new provider selects different proved Stock code.

The packet contains 19 new Lean files and one audit file.
Its only call-class foundation is the landed PR911 interface.
It imports no unpublished result-call consumer module.
The immutable manifest records the complete 808-source closure on main 84b384b264a32e4b0bc9663f22f2a8b0464e5767.

The focused current-main gate checks every external provider with native Lake keys.
It builds every new module with native Lake keys, one job, and a 2 GiB cap.
The audit checks 44 standard roots and three marked fixed roots.
The preserved-context audit passed before the current-main gate.

This packet does not activate the new class in the three production CLIs.
The complete compiler, checker, generated-proof, and linked ARM matrix remains required.
The separate production integration preserves the complete previous file action and all typed modes.
The full original #140 goal remains incomplete.
