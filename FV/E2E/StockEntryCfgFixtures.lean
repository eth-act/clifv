import FV.E2E.StockCfgFixtures

namespace E2E.StockEntryCfgNIWitness
open Backend.Stock.D0
set_option autoImplicit false

/-- Actual dividing entry bodies with inherited values, nonempty copies,
nine ABI parameters and the original placed source slot. Mode3 distinguishes
an early zero-divisor trap from a later signed-overflow trap. -/
def function (config : Configuration) (ty : Clif.Ty) (mode : Nat) : Clif.Function :=
  let old := StockCfgNIWitness.function config ty 0
  let target : List Clif.Stmt :=
    if mode == 0 then
      [⟨[102],.binary .iadd ty 1 101⟩,⟨[103],.binary .rotl ty 102 8⟩,⟨[104],.bmask ty 103⟩]
    else if mode == 1 then [⟨[102],.binary .iadd ty 1 101⟩]
    else if mode == 2 then [⟨[102],.iconst ty 0⟩,⟨[103],.div .udiv ty 101 102⟩]
    else [⟨[102],.iconst ty (BitVec.ofNat ty.width (2^(ty.width-1)))⟩,
      ⟨[103],.iconst ty (BitVec.ofNat ty.width (2^ty.width-1))⟩,⟨[104],.div .sdiv ty 102 103⟩]
  {old with blocks := [
    {old.blocks[0]! with body := [⟨[100],.div (if mode == 1 then .sdiv else .udiv) ty 1 8⟩,⟨[],.nop⟩]},
    {old.blocks[1]! with body := target,term := .ret [if mode == 1 then 102 else if mode == 2 then 103 else 104]}]}

def functions (config : Configuration) : List (Clif.Function × Clif.Ty) :=
  let all := ([.i8,.i16,.i32,.i64] : List Clif.Ty).flatMap fun ty =>
    (List.range 4).map fun mode => (function config ty mode,ty)
  all.zipIdx.map fun ((f,ty),i) => ({f with name := s!"stock_cfgentry_{i}"},ty)

/-- Broader entry bodies retain the original dividing-entry cohort verbatim.
The additional cases exercise all existing scalar families at four widths. -/
def scalarFunction (config : Configuration) (ty : Clif.Ty) (kind : Nat) : Clif.Function :=
  let old := StockCfgNIWitness.function config ty 0
  let inst : Clif.Inst :=
    match kind with
    | 0 => .binary .iadd ty 1 8
    | 1 => .binary .isub ty 1 8
    | 2 => .select ty 0 1 8
    | 3 => .binary .band ty 1 8
    | 4 => .binary .bor ty 1 8
    | 5 => .binary .bxor ty 1 8
    | 6 => .unary .bnot ty 1
    | 7 => .binary .imul ty 1 8
    | 8 => .binary .ishl ty 1 8
    | 9 => .binary .sshr ty 1 8
    | 10 => .binary .rotl ty 1 8
    | 11 => .unary .ineg ty 1
    | 12 => .unary .clz ty 1
    | 13 => .unary .popcnt ty 1
    | 14 => .binary .smin ty 1 8
    | 15 => .icmp .slt ty 1 8
    | 16 => .binary .umulhi ty 1 8
    | 17 => .bmask ty 1
    | 18 => if ty == .i64 then .ireduce .i32 1 else .extend .uextend .i64 1
    | _ => .extend .uextend .i64 200
  let retTy := if kind == 15 then Clif.Ty.i8 else if kind == 18 then
    (if ty == .i64 then Clif.Ty.i32 else Clif.Ty.i64) else if kind == 19 then Clif.Ty.i64 else ty
  let body := (if kind == 19 then [⟨[200],.icmp .slt ty 1 8⟩] else []) ++ [⟨[100],inst⟩,⟨[],.nop⟩]
  {old with
    sig := {old.sig with returns := [⟨retTy,.none,.normal⟩]}
    blocks := [
      {old.blocks[0]! with body,term := .jump ⟨10,if kind == 19 then [100,200] else [100]⟩},
      {id := 10,params := [(101,retTy)] ++ (if kind == 19 then [(201,.i8)] else []),
        body := if retTy == ty then [⟨[102],.binary .iadd ty 1 101⟩] else [],
        term := .ret [if retTy == ty then 102 else 101]}]}

def scalarFunctions (config : Configuration) : List (Clif.Function × Clif.Ty) :=
  let added := ([.i8,.i16,.i32,.i64] : List Clif.Ty).flatMap fun ty =>
    (List.range 20).map fun kind => (scalarFunction config ty kind,ty)
  (functions config ++ added).zipIdx.map fun ((f,ty),i) => ({f with name := s!"stock_cfgscalarentry_{i}"},ty)

end E2E.StockEntryCfgNIWitness
