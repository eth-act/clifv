Physical return checks now reuse one program cache for artifact lookups, symbols, target pins, ABI arities, and direct targets. Pin calculation starts only when a call needs the target. Universal equality proves that the compiled checker keeps every canonical verdict, including duplicate names and failed pipeline entries.

The unchanged sret capture passes in both cleanup modes. The real mixed caller still fails its physical return check in both modes. This change adds no production selector or accepted-input restriction.

Validation: the 1,729-module focused closure and all 12 audit roots pass on dd56ea3a. All 20 prior axiom sets remain exact. Worker-A gave one QUICK, DIRTY, CHEAP direct review. No review agents or review builds ran. Current-main validation waits for worker-A's shared #824 table rebuild, so we do not duplicate that build.

Continues #140. Default sret activation, caller alignment, and the remaining original obligations stay open.
