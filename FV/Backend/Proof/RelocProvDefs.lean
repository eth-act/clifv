module

public import FV.Backend.Encode
public import FV.Backend.Isel

@[expose] public section

/-!
# Name provenance of the compiled relocations: the definitions (L1e, #216)

The compiled code of a CLIF function `f` relocates only against names and offsets of `f`'s own
declarations:

* `externNames f`: the names of its external function declarations (`fnN = %name(sig)`), the
  only names `func_ref_data` gives (`call`, `try_call`, `func_addr`);
* `gvRefs f`: its `symbol`/`symbol tls` global values with their offsets, the only names and
  offsets `symbol_value_data` gives (`symbol_value`, `tls_value`);
* `refOffs f`: the offsets an address load can carry (`0`, from `func_addr`/calls, and the
  global values' offsets).

`RefsOk f m`: instruction `m`'s references are `f`'s (a call's symbol is an external function's
name; an address load's name is a declared name, its offset a declared offset).
`RelocOk f r`: a relocation's symbol (and addend) are `f`'s, by type (`bl`: an external
function's name; a page pair: a declared name and offset).
-/

namespace Backend.Proof.RelocProv

open Backend Isle Isle.Aarch64

/-- The names of `f`'s external function declarations. -/
def externNames (f : Clif.Function) : List String := f.externs.map (·.2.name)

/-- `f`'s `symbol` and `symbol tls` global values: name and offset. -/
def gvRefs (f : Clif.Function) : List (String × Int) :=
  f.globals.filterMap fun g => match g.2 with
    | .symbol n off _ => some (n, off)
    | .tlsSymbol n off _ => some (n, off)
    | _ => none

/-- The names of `f`'s symbol global values. -/
def gvNames (f : Clif.Function) : List String := (gvRefs f).map (·.1)

/-- Every name `f` declares (external functions, symbol global values). -/
def refNames (f : Clif.Function) : List String := externNames f ++ gvNames f

/-- The offsets an address load of `f` can carry: `0` and the global values' offsets. -/
def refOffs (f : Clif.Function) : List Int := 0 :: (gvRefs f).map (·.2)

/-- **The references of an instruction are `f`'s.** -/
def RefsOk (f : Clif.Function) : MInst → Prop
  | .call c => ∀ n, c.dest = .sym n → n ∈ externNames f
  | .tryCall c _ => ∀ n, c.dest = .sym n → n ∈ externNames f
  | .loadExtNameGot _ n => n ∈ refNames f
  | .loadExtNameNear _ n o => n ∈ refNames f ∧ o ∈ refOffs f
  | _ => True

/-- Every instruction of the VCode satisfies `P`. -/
def AllInsts (P : MInst → Prop) (vc : VCode) : Prop :=
  ∀ b ∈ vc.blocks.toList, ∀ m ∈ b.insts.toList, P m

/-- **A relocation's symbol and addend are `f`'s**: a `bl`'s symbol is an external function's
name, a page pair's symbol and addend are a declared name and offset. -/
def RelocOk (f : Clif.Function) (r : Reloc) : Prop :=
  match r.type with
  | .call26 => r.sym ∈ externNames f
  | .adrGotPage | .adrPrelPgHi21 => r.sym ∈ refNames f ∧ r.addend ∈ refOffs f
  | _ => True

/-! ## Atoms of ISLE values -/

/-- The names inside an operand: an external name, a call's symbol. -/
def opNames : Opnd → List String
  | .extName n => [n]
  | .callInfo c => match c.dest with
    | .sym n => [n]
    | .reg _ => []
  | _ => []

mutual
/-- The names inside a value. -/
def vNames : V → List String
  | .op o => opNames o
  | .data _ _ fs => vNamesL fs
  | _ => []
/-- The names inside a list of values. -/
def vNamesL : List V → List String
  | [] => []
  | v :: vs => vNames v ++ vNamesL vs
end

mutual
/-- The integer leaves of a value. -/
def vInts : V → List Int
  | .int i => [i]
  | .data _ _ fs => vIntsL fs
  | _ => []
/-- The integer leaves of a list of values. -/
def vIntsL : List V → List Int
  | [] => []
  | v :: vs => vInts v ++ vIntsL vs
end

mutual
/-- Every `MInst` inside the value has its references in `f`. -/
def VGood (f : Clif.Function) : V → Prop
  | .data t k fs => (t = tyMInst → ∀ m, MInst.ofV (.data t k fs) = some m → RefsOk f m) ∧ VGoodL f fs
  | _ => True
/-- `VGood` of every value of a list. -/
def VGoodL (f : Clif.Function) : List V → Prop
  | [] => True
  | v :: vs => VGood f v ∧ VGoodL f vs
end

end Backend.Proof.RelocProv
