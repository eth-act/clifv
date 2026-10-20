import FV.Clif.Run

set_option autoImplicit false
namespace Clif.StockPrologueSource

def source (name : String) (runs : List RunCommand) : Function := {
  name, runs
  sig := {
    params := [⟨.i64, .none, .normal⟩]
    returns := [⟨.i64, .none, .normal⟩]
    callConv := some .systemV }
  blocks := [
    {id := 0, params := [(0, .i64)], body := [{inst := .nop}], term := .jump {block := 1, args := []}},
    {id := 1, body := [{inst := .nop}], term := .ret [0]}] }

def argument (word : BitVec 64) : Val := ⟨.i64, word⟩
def frame (name : String) (runs : List RunCommand) (word : BitVec 64) : Frame := {
  func := source name runs, slots := [], body := [{inst := .nop}],
  term := .jump {block := 1, args := []}, regs := Regs.empty.set 0 (argument word) }

private theorem slots_empty (name : String) (runs : List RunCommand) (mem : Mem) :
    (enterSlots (source name runs) mem).1 = [] := by
  unfold enterSlots
  cases h : mem.place with
  | none => rfl
  | some pl =>
    dsimp only
    cases h' : pl.frame (source name runs).name with
    | none => rfl
    | some pair => rcases pair with ⟨d, off⟩; rfl

theorem source_entry (name : String) (runs : List RunCommand)
    (word : BitVec 64) (mem : Mem) :
    enterFunc (source name runs) [argument word] mem =
      .ok (frame name runs word, (enterSlots (source name runs) mem).2) := by
  simp [enterFunc, checkTys, AbiParam.tys, Function.entry?, source, argument, frame,
    Regs.setMany, Res.ofOption, Res.check]
  exact slots_empty name runs mem

/-- All four actual source steps, for every input word, environment and memory. -/
theorem source_body (name : String) (runs : List RunCommand) (word : BitVec 64)
    (mem : Mem) (env : Env) (p : Program) :
    runLoop env p 4 ⟨frame name runs word, [], mem⟩ =
      .returned [argument word] (mem.free []).leave := by
  rfl

theorem source_memory_roundtrip (name : String) (runs : List RunCommand) (mem : Mem) :
    (((enterSlots (source name runs) mem).2).free []).leave = mem := by
  cases mem with
  | mk allocs bytes next symbols place =>
    cases place with
    | none => simp [enterSlots, source, bumpSlots, Mem.free, Mem.leave]
    | some pl =>
      cases h : pl.frame name with
      | none => simp [enterSlots, source, h, bumpSlots, Mem.free, Mem.leave]
      | some pair =>
        rcases pair with ⟨d, off⟩
        simp [enterSlots, source, h, placeSlots, Mem.free, Mem.leave]

/-- An inhabited whole source-function execution; no oracle or memory premise. -/
theorem complete_source_witness (name : String) (runs : List RunCommand)
    (word : BitVec 64) (mem : Mem) :
    ∃ (fr : Frame) (entered : Mem),
      enterFunc (source name runs) [argument word] mem = .ok (fr, entered) ∧
      runLoop Env.empty {funcs := [source name runs]} 4 ⟨fr, [], entered⟩ =
        .returned [argument word] mem := by
  refine ⟨frame name runs word, (enterSlots (source name runs) mem).2,
    source_entry name runs word mem, ?_⟩
  rw [source_body, source_memory_roundtrip]

end Clif.StockPrologueSource
