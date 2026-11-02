import FV.Clif.Run

/-!
# Renaming the names of a CLIF program (T7d, docs/contracts/frontend.md)

A CLIF program refers to code and data by **name** in five places only: a function's own name,
its extern declarations (`fnN = %name(…)`, called by `call`/`return_call`/`try_call`, taken by
`func_addr`), its symbol global values (`gvN = symbol %name`, `tls %name`), its run commands, and
the data objects (their names and the `%name` targets of their relocations). Everything else
(values, blocks, slots, `FnRef`s, `sigN`) is local to a function and numbered.

* `Function.rename g`, `Program.rename g`, `DataObject.rename g`: apply `g : String → String`
  to exactly those names. `Function.names`/`DataObject.names` list them.
* `Ren`: a bijection of `String` (`fwd` with its inverse `bwd`). For a bijection the run-time
  objects that are keyed by name are renamed too: the memory's link-time symbol table
  (`Mem.symbols`) and slot-placement oracle (`Mem.place`), the frames' functions, the
  environment of outside code (`Env.ren`: an outside function of the renamed program is the
  original one at the original name, run on the un-renamed memory).
* `Outcome.erase`: an outcome with the message of `stuck` forgotten (the messages name the
  function or symbol at fault).

`FV/Front/RenameRun.lean` proves that renaming commutes with the semantics
(`Clif.runLoop_ren`).
-/

namespace Clif

/-! ## The syntax -/

/-- Rename the symbol of a global value. -/
def GlobalValue.rename (g : String → String) : GlobalValue → GlobalValue
  | .symbol n off c => .symbol (g n) off c
  | .tlsSymbol n off c => .tlsSymbol (g n) off c
  | v => v

/-- Rename an extern declaration's callee. -/
def ExtFunc.rename (g : String → String) (e : ExtFunc) : ExtFunc := { e with name := g e.name }

/-- Rename a run command's function. -/
def RunCommand.rename (g : String → String) (r : RunCommand) : RunCommand :=
  { r with func := g r.func }

/-- **Rename every name of a function**: its own, its extern declarations', its global values'
symbols, its run commands'. -/
def Function.rename (g : String → String) (f : Function) : Function :=
  { f with
    name := g f.name
    globals := f.globals.map fun p => (p.1, p.2.rename g)
    externs := f.externs.map fun p => (p.1, p.2.rename g)
    runs := f.runs.map (·.rename g) }

/-- Rename a relocation's target. -/
def DataItem.rename (g : String → String) : DataItem → DataItem
  | .addr n off => .addr (g n) off
  | i => i

/-- Rename a data object and its relocations' targets. -/
def DataObject.rename (g : String → String) (o : DataObject) : DataObject :=
  { o with name := g o.name, items := o.items.map (·.rename g) }

/-- Rename every name of a program. -/
def Program.rename (g : String → String) (p : Program) : Program :=
  { p with data := p.data.map (·.rename g), funcs := p.funcs.map (·.rename g) }

/-- The symbol a global value names. -/
def GlobalValue.name? : GlobalValue → Option String
  | .symbol n _ _ | .tlsSymbol n _ _ => some n
  | _ => none

/-- **The names of a function** (those `Function.rename` renames). -/
def Function.names (f : Function) : List String :=
  f.name :: (f.externs.map (·.2.name) ++ f.globals.filterMap (·.2.name?) ++ f.runs.map (·.func))

/-- The target of a relocation. -/
def DataItem.name? : DataItem → Option String
  | .addr n _ => some n
  | _ => none

/-- The relocation targets of a data object. -/
def DataObject.refs (o : DataObject) : List String := o.items.filterMap (·.name?)

/-- **The names of a data object** (those `DataObject.rename` renames). -/
def DataObject.names (o : DataObject) : List String := o.name :: o.refs

/-! ## Bijections of names -/

/-- A bijection of `String`: `fwd` and its inverse `bwd`. -/
structure Ren where
  fwd : String → String
  bwd : String → String
  bwd_fwd : ∀ x, bwd (fwd x) = x
  fwd_bwd : ∀ y, fwd (bwd y) = y

namespace Ren

/-- The identity. -/
protected def id : Ren := ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩

/-- The inverse. -/
def symm (σ : Ren) : Ren := ⟨σ.bwd, σ.fwd, σ.fwd_bwd, σ.bwd_fwd⟩

/-- `σ` then `τ`. -/
def trans (σ τ : Ren) : Ren where
  fwd x := τ.fwd (σ.fwd x)
  bwd y := σ.bwd (τ.bwd y)
  bwd_fwd x := by simp only [τ.bwd_fwd, σ.bwd_fwd]
  fwd_bwd y := by simp only [σ.fwd_bwd, τ.fwd_bwd]

theorem fwd_inj (σ : Ren) {x y : String} (h : σ.fwd x = σ.fwd y) : x = y := by
  rw [← σ.bwd_fwd x, h, σ.bwd_fwd]

theorem fwd_eq_iff (σ : Ren) {x y : String} : σ.fwd x = σ.fwd y ↔ x = y :=
  ⟨σ.fwd_inj, fun h => h ▸ rfl⟩

@[simp] theorem symm_fwd (σ : Ren) : σ.symm.fwd = σ.bwd := rfl
@[simp] theorem symm_bwd (σ : Ren) : σ.symm.bwd = σ.fwd := rfl

end Ren

/-! ## The run-time objects -/

/-- Rename the names memory is keyed by: the link-time symbol table, the slot-placement
oracle's frames. -/
def Mem.ren (σ : Ren) (m : Mem) : Mem :=
  { m with
    symbols := fun n => m.symbols (σ.bwd n)
    place := m.place.map fun pl => { pl with frame := fun n => pl.frame (σ.bwd n) } }

/-- Rename an activation's function. -/
def Frame.ren (σ : Ren) (fr : Frame) : Frame := { fr with func := fr.func.rename σ.fwd }

/-- Rename a state: its frames' functions and its memory. -/
def State.ren (σ : Ren) (s : State) : State where
  frame := s.frame.ren σ
  callers := s.callers.map fun c => (c.1.ren σ, c.2)
  mem := s.mem.ren σ

/-- Rename the memory of a returned outcome. -/
def Outcome.ren (σ : Ren) : Outcome → Outcome
  | .returned vals m => .returned vals (m.ren σ)
  | o => o

/-- Forget the message of a `stuck` outcome. -/
def Outcome.erase : Outcome → Outcome
  | .stuck _ => .stuck ""
  | o => o

/-- **The environment of the renamed program**: the outside function at a renamed name is the
original one at the original name, run on the memory with the original names; the further code
names and the known signatures likewise. -/
def Env.ren (σ : Ren) (E : Env) : Env where
  extern n := (E.extern (σ.bwd n)).map fun h vals m => (h vals (m.ren σ.symm)).ren σ
  names := E.names.map σ.fwd
  sigOf n := E.sigOf (σ.bwd n)

end Clif
