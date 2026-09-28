import FV.Isle.Opt.Simplify

/-!
# A toy e-graph for testing `Isle.Opt.simplify`

Values are indices into `nodes`/`types`; every value has the nodes listed for it (block
parameters have none). `make` hash-conses: a node equal to an existing single-node value's
node returns that value, otherwise it appends a new value.
-/

namespace Isle.Opt.Toy
open Isle.Opt

structure G where
  nodes : Array (List Clif.Inst)
  types : Array (Option Clif.Ty)
  deriving Repr

/-- Result type of a node (`Clif.Inst` records the operand type of `icmp`/`iconcat`). -/
def resultTy : Clif.Inst → Option Clif.Ty
  | .iconst t _ | .unary _ t _ | .binary _ t _ _ | .select t .. | .selectSpectreGuard t ..
  | .bitselect t .. | .bmask t _ | .extend _ t _ | .ireduce t _ | .stackAddr t .. | .symbolValue t _ =>
    some t
  | .icmp .. => some .i8
  | .iconcat t _ _ => t.double?
  | _ => none

def enodes (g : G) (v : Nat) : List Clif.Inst := (g.nodes[v]?).getD []
def typeOf (g : G) (v : Nat) : Option Clif.Ty := (g.types[v]?).join

def make (g : G) (i : Clif.Inst) : Nat × G :=
  match (List.range g.nodes.size).find? (fun v => enodes g v == [i]) with
  | some v => (v, g)
  | none => (g.nodes.size, { nodes := g.nodes.push [i], types := g.types.push (resultTy i) })

/-- A graph from `(type, nodes)` per value. -/
def mk (vs : List (Clif.Ty × List Clif.Inst)) : G :=
  ⟨vs.toArray.map (·.2), vs.toArray.map (some ·.1)⟩

/-- `simplify` on value `v`: `(candidates, rule names)`, and the grown graph. -/
def run (g : G) (v : Nat) : Except String (List (Nat × Bool) × List String × G) :=
  simplify enodes typeOf make g v

end Isle.Opt.Toy
