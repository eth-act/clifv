import FV.E2E.UnwindMemoryFaultObservation

namespace E2E.UnwindCaughtMemoryWitness
set_option autoImplicit false

/-- A separate diagnostic function. It does not replace any preserved capture. -/
def signature : Clif.Signature := {
  params := [{ty := .i64}],returns := [{ty := .i64}],callConv := some .systemV }

def table : Clif.ExnTable := {
  sig := 0,normal := {block := 1,args := [.ret 0]},
  items := [.tag 0 {block := 2,args := [.exn 0]}] }

def function : Clif.Function := {
  name := "caught_then_store",sig := signature,
  externs := [(0,{name := "raise",sig := signature})],sigDecls := [(0,signature)],
  blocks := [
    {id := 0,params := [(0,.i64)],term := .tryCall 0 [0] table},
    {id := 1,params := [(1,.i64)],term := .ret [1]},
    {id := 2,params := [(2,.i64)],body := [⟨[],.store .store .i64 {} 0 2 0⟩],term := .ret [0]}] }

def program : Clif.Program := {funcs := [function]}
def value (word : BitVec 64) : Clif.Val := ⟨.i64,word⟩
def exception : Clif.Exn := ⟨fun tag => tag == 0,[value 0]⟩
def environment : Clif.XEnv := {extern := fun _ => some fun _ memory => .unwound exception memory}

def initial (word : BitVec 64) : Clif.State := {
  frame := {func := function,regs := Clif.Regs.empty.set 0 (value word),slots := [],
    body := [],term := .tryCall 0 [0] table},callers := [],mem := Clif.Mem.empty }

def caught (word : BitVec 64) : Clif.XState := {
  s := {initial word with frame := {(initial word).frame with
    regs := (initial word).frame.regs.set 3 (value 0),term := .jump {block := 2,args := [3]}}},
  tries := [] }

def atStore (word : BitVec 64) : Clif.XState := {
  s := {(caught word).s with frame := {(caught word).s.frame with
    regs := (caught word).s.frame.regs.set 2 (value 0),
    body := [⟨[],.store .store .i64 {} 0 2 0⟩],term := .ret [0]}},tries := [] }

/-- The actual unwind catches the exception and enters the later memory instruction. -/
theorem handler_reached (word : BitVec 64) :
    ReachX environment program (initial word).toX (atStore word) := by
  exact .step (show Clif.stepX environment program (initial word).toX = .next (caught word) from rfl)
    (.step (show Clif.stepX environment program (caught word) = .next (atStore word) from rfl)
      (.refl _))

/-- The handler keeps default trapping flags and stores through the caught zero pointer. -/
theorem handler_memory_event (word : BitVec 64) :
    Clif.MemTrapAt environment.toEnv program (atStore word).s .heapOob 0 8 := by
  exact ⟨rfl,rfl,⟨⟨[],.store .store .i64 {} 0 2 0⟩,[],rfl,.store (pv := value 0) rfl⟩⟩

theorem caught_then_source_fault (word : BitVec 64) :
    UnwindMemoryFaultEvent environment program (initial word) .heapOob :=
  ⟨atStore word,0,8,handler_reached word,handler_memory_event word⟩

/-- This case is excluded by the actual old theorem, rather than contradicting it. -/
theorem original_admission_excludes (word : BitVec 64) :
    ¬ TrapsExplicitX environment program (initial word) := by
  intro admitted
  exact admitted.no_memory_event (handler_reached word) (handler_memory_event word)

/-- The separate source observation gives the actual source trap after the caught exception. -/
theorem caught_source_run (word : BitVec 64) :
    ∃ fuel, Clif.runLoopX environment program fuel (initial word).toX = .trapped .heapOob :=
  (caught_then_source_fault word).source_trapped

end E2E.UnwindCaughtMemoryWitness
