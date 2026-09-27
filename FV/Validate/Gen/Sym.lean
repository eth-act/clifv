/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license.

# Untrusted value numbering with sample vectors

The proof generator reasons about Arm and CLIF values by *value numbering*: every value it
meets is a node of an arena, and every node carries its value in each of `nSamples` random
samples of the atoms (the values at the last cut point). Two nodes "agree" when their sample
vectors agree. This is only a heuristic to decide what to claim; every claim is proven by the
generated Lean proof, so a wrong guess makes a proof fail, never a wrong VALID.
-/
namespace Validate.Gen

/-- Number of random samples per node. -/
def nSamples : Nat := 48

/-- How a node can be printed as a Lean term of type `BitVec 64` (if at all). -/
inductive Shape where
  /-- A constant. -/
  | const (v : BitVec 64)
  /-- A named atom: `term` is its Lean term; only its low `w` bits are meaningful. -/
  | atom (term : String) (w : Nat)
  /-- `base + off` for a printable node `base`. -/
  | offset (base : Nat) (off : BitVec 64)
  /-- Anything else. -/
  | other
  deriving Inhabited

structure Node where
  shape : Shape
  vals : Array (BitVec 64)
  deriving Inhabited

/-- Node arena. -/
structure Arena where
  nodes : Array Node := #[]
  /-- Next pseudo-random seed. -/
  seed : UInt64 := 0x9e3779b97f4a7c15
  deriving Inhabited

abbrev SymM := StateT Arena (Except String)

def fail {α : Type} (msg : String) : SymM α := throw msg

/-- xorshift64* -/
def nextRand : SymM UInt64 := do
  let s ← get
  let mut x := s.seed
  x := x ^^^ (x >>> 12)
  x := x ^^^ (x <<< 25)
  x := x ^^^ (x >>> 27)
  set { s with seed := x }
  return x * 0x2545F4914F6CDD1D

def node (i : Nat) : SymM Node := do
  match (← get).nodes[i]? with
  | some n => pure n
  | none => fail s!"internal: no node {i}"

def vals (i : Nat) : SymM (Array (BitVec 64)) := return (← node i).vals

def addNode (n : Node) : SymM Nat := do
  let s ← get
  set { s with nodes := s.nodes.push n }
  return s.nodes.size

def mkConst (v : BitVec 64) : SymM Nat :=
  addNode { shape := .const v, vals := Array.replicate nSamples v }

def constOf? (i : Nat) : SymM (Option (BitVec 64)) := do
  match (← node i).shape with
  | .const v => pure (some v)
  | _ => pure none

/-- Low `w` bits, zero-extended. -/
def maskW (w : Nat) (x : BitVec 64) : BitVec 64 := if w ≥ 64 then x else (x.setWidth w).setWidth 64

/-- A fresh atom whose low `w` bits are sampled (biased towards edge values) and whose upper
bits are random. -/
def mkAtom (term : String) (w : Nat) (upperJunk : Bool := true) : SymM Nat := do
  let mut vs := #[]
  for k in [0:nSamples] do
    let r ← nextRand
    let r2 ← nextRand
    let lo : BitVec 64 := match k % 6 with
      | 0 => BitVec.ofNat 64 (r.toNat % 4)
      | 1 => BitVec.ofNat 64 (r.toNat % 3) - 1#64   -- -1, 0, 1
      | 2 => match r.toNat % 6 with
        | 0 => BitVec.ofNat 64 (2 ^ (w - 1))                -- MIN
        | 1 => BitVec.ofNat 64 (2 ^ (w - 1) - 1)            -- MAX
        | 2 => BitVec.ofNat 64 (2 ^ w - 1)                  -- -1
        | 3 => BitVec.ofNat 64 (2 ^ (w - 1) + 1)
        | 4 => BitVec.ofNat 64 (r2.toNat % 256)
        | _ => BitVec.ofNat 64 (2 ^ w - 2)
      | 3 => BitVec.ofNat 64 (r.toNat % 17)
      | _ => BitVec.ofNat 64 r.toNat
    let v := if upperJunk && w < 64 then
      (maskW w lo) ||| ((BitVec.ofNat 64 r2.toNat) &&& ~~~(maskW w (BitVec.allOnes 64)))
    else maskW w lo
    vs := vs.push v
  addNode { shape := .atom term w, vals := vs }

/-- A fresh atom with explicit sample values. -/
def mkAtomVals (term : String) (w : Nat) (vs : Array (BitVec 64)) : SymM Nat :=
  addNode { shape := .atom term w, vals := vs }

/-- A 64-bit address-like atom: 16-byte aligned, in a high region (like a stack pointer). -/
def mkSpAtom (term : String) : SymM Nat := do
  let mut vs := #[]
  for _ in [0:nSamples] do
    let r ← nextRand
    vs := vs.push (BitVec.ofNat 64 (0x7ff000000000 + (r.toNat % 0x10000000) * 16))
  addNode { shape := .atom term 64, vals := vs }

/-- Apply a unary operation. -/
def op1 (f : BitVec 64 → BitVec 64) (a : Nat) : SymM Nat := do
  let na ← node a
  match na.shape with
  | .const x => mkConst (f x)
  | _ => addNode { shape := .other, vals := na.vals.map f }

/-- Apply a binary operation. -/
def op2 (f : BitVec 64 → BitVec 64 → BitVec 64) (a b : Nat) : SymM Nat := do
  let na ← node a
  let nb ← node b
  match na.shape, nb.shape with
  | .const x, .const y => mkConst (f x y)
  | _, _ => addNode { shape := .other, vals := (na.vals.zip nb.vals).map fun (x, y) => f x y }

/-- Apply a ternary operation. -/
def op3 (f : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64) (a b c : Nat) : SymM Nat := do
  let na ← node a
  let nb ← node b
  let nc ← node c
  match na.shape, nb.shape, nc.shape with
  | .const x, .const y, .const z => mkConst (f x y z)
  | _, _, _ =>
    let mut vs := #[]
    for k in [0:nSamples] do
      vs := vs.push (f na.vals[k]! nb.vals[k]! nc.vals[k]!)
    addNode { shape := .other, vals := vs }

/-- `a + c` for a constant `c`, keeping a printable shape. -/
def addConst (a : Nat) (c : BitVec 64) : SymM Nat := do
  if c == 0 then return a
  let na ← node a
  match na.shape with
  | .const x => mkConst (x + c)
  | .offset b o => addNode { shape := .offset b (o + c), vals := na.vals.map (· + c) }
  | .atom .. => addNode { shape := .offset a c, vals := na.vals.map (· + c) }
  | .other => addNode { shape := .other, vals := na.vals.map (· + c) }

/-- Do the low `w` bits of nodes `a` and `b` agree in every sample? -/
def agree (w : Nat) (a b : Nat) : SymM Bool := do
  let va ← vals a
  let vb ← vals b
  return (va.zip vb).all fun (x, y) => maskW w x == maskW w y

/-- Is the low-`w`-bit value of `a` the same in every sample? -/
def isConstW (w : Nat) (a : Nat) : SymM (Option (BitVec 64)) := do
  let va ← vals a
  match va[0]? with
  | none => pure none
  | some v0 => pure (if va.all (maskW w · == maskW w v0) then some (maskW w v0) else none)

/-- Does `a - b` have the same value in every sample? Returns it. -/
def constDiff (a b : Nat) : SymM (Option (BitVec 64)) := do
  let va ← vals a
  let vb ← vals b
  let ds := (va.zip vb).map fun (x, y) => x - y
  match ds[0]? with
  | none => pure none
  | some d => pure (if ds.all (· == d) then some d else none)

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- Lean term of a printable node, as a `BitVec 64`. -/
partial def printNode (i : Nat) : SymM (Option String) := do
  match (← node i).shape with
  | .const v => pure (some s!"({hex v.toNat}#64)")
  | .atom t _ => pure (some t)
  | .offset b o =>
    match ← printNode b with
    | some t =>
      if o.msb then pure (some s!"({t} - {hex (0 - o).toNat}#64)")
      else pure (some s!"({t} + {hex o.toNat}#64)")
    | none => pure none
  | .other => pure none

end Validate.Gen
