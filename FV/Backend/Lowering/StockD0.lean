module

public import FV.Backend.Lowering.Stock

public section

namespace Backend.Stock.D0

@[expose] section
inductive Configuration where
  | defaultI32 | systemVI32 | fastI32 | defaultI64 | systemVI64 | fastI64
  deriving DecidableEq, Repr, Inhabited
end

def configurations : List Configuration := [.defaultI32, .systemVI32, .fastI32, .defaultI64, .systemVI64, .fastI64]
def valueType : Configuration → Clif.Ty
  | .defaultI32 | .systemVI32 | .fastI32 => .i32
  | .defaultI64 | .systemVI64 | .fastI64 => .i64
def convention : Configuration → Option Clif.CallConv
  | .defaultI32 | .defaultI64 => none
  | .systemVI32 | .systemVI64 => some .systemV
  | .fastI32 | .fastI64 => some .fast

/-- Structural class with arbitrary symbol names and filetest metadata. -/
def source (name : String) (c : Configuration) (runs : List Clif.RunCommand := []) : Clif.Function := {
  name
  sig := { params := [⟨valueType c, .none, .normal⟩],
           returns := [⟨valueType c, .none, .normal⟩], callConv := convention c }
  blocks := [{ id := 0, params := [(0, valueType c)], term := .ret [0] }]
  runs }

def eligible (f : Clif.Function) : Bool :=
  configurations.any fun c => decide (f = source f.name c f.runs)

def denseReg : Reg → Reg
  | .vreg n cls => .vreg (n - firstUserVreg) cls
  | r => r

def denseCode (vc : VCode) : VCode := {
  vc with
  classes := vc.classes.extract firstUserVreg vc.classes.size
  blocks := vc.blocks.map fun b => { b with
    insts := b.insts.map (·.mapRegs denseReg)
    params := b.params.map denseReg
    branchArgs := b.branchArgs.map denseReg } }

def compact (name : String) (r : Result) : VCode := {denseCode r.code with name}

@[expose] section
inductive Origin where
  | stockD0 | legacy
  deriving DecidableEq, Repr, Inhabited
end

/-- Internal origin metadata for proving and testing the fixed dispatcher. -/
def selectWith (stock : Clif.Function → Except String Result) (f : Clif.Function) :
    Except String (Origin × VCode) :=
  let legacy := fun (_ : Unit) => (lowerFunction f).map fun vc => (Origin.legacy, vc)
  if eligible f then
    match stock f with
    | .ok r =>
      if r.edgeArgs.all (·.isEmpty) then .ok (.stockD0, compact f.name r)
      else legacy ()
    | .error _ => legacy ()
  else legacy ()

def defaultLower (f : Clif.Function) : Except String VCode :=
  (selectWith Stock.lower f).map Prod.snd

end Backend.Stock.D0
