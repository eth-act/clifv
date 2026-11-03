/-- **The slots are outside the caller's stack and CLIF memory**: what the outside caller of
`OutsideCall` (stack `N`) guarantees about the addresses `S` besides the code: none is in the free
stack, in a stack argument, or in a live CLIF allocation. -/
structure OutsideAvoids (S : BitVec 64 → Prop) (f : Clif.Function) (N : Nat) (r : Arm.ArmState)
    (args : List Clif.Val) (cm : Clif.Mem) : Prop where
  stack : ∀ a, S a → ¬ StackBelow N (spv r) a
  args : ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args →
    Avoids S v.ty.bytes (spv r + BitVec.ofNat 64 off)
  valid : ∀ a n, cm.valid a n = true → ∀ k < n, ¬ S (BitVec.ofNat 64 (a + k))

