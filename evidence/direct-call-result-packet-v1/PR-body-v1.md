Stock’s direct scalar calls lacked a proved connection between source results, virtual definitions, and physical return registers. This change adds that adapter through the existing callee contract and allocation checks.

The complete caller uses source result 31, mapped register 193, and virtual destination 194. Its call definition and return use x0. The witness covers external continuation and internal callee return with arbitrary i64 arguments. The generic adapter preserves arbitrary callee memory effects.

The fixture uses an opaque Boolean and abstract Except elimination to bound elaboration. Existing theorem variants, axioms, callbacks, and production routes remain unchanged. Function-domain integration and production activation follow in the next batch.

Validation:

- The unchanged audit passed eleven standard-only roots and two marked fixed roots.
- The complete source witness and arbitrary-memory theorem passed.
- Final focused builds peaked at 256,344,064 bytes, with no OOM event.
- The frozen source view remains clean. Unique evidence remains saved; isolated build outputs were removed.
