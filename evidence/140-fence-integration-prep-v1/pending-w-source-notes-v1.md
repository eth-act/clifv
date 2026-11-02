# Pending executable transfer

The four new W adapters retain every old interface.
The generic access adapter preserves arbitrary stronger trace invariants.
The adapters use the existing q_initW and realizes_value_allW proofs.
The original-source adapter uses the proved legalization identity.
It does not require NoMemTrap.

The remaining executable proof must retain every earlier access.
GoodX alone does not provide the memory-write fact.
GoodXW adds WritesAt.
The existing evsOkAt_of_goodW proof uses that fact and original MapRelRW.
The transfer must use the actual Stock results through WithResults/Semantic consumers.
The old DeadCleanupBinary.sys uses resultsCleanup and cannot identify different Stock artifacts.
No source equality alone justifies this conversion.

The broad normal queue owns the missing W and executable providers.
This worker must borrow only completed coherent outputs after normal-key checks.
The four prepared modules remain unverified.
Actual executable, source/peak, generated proof and production coverage remain incomplete.
