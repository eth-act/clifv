import FV.Backend.Proof.StockMemorySinkExtCheck

/-! Non-vacuity of the executable selector and check on Cranelift's
`%load_uextend_i8_i32` and `%load_sextend_i16_i64` (`load-extends.clif`, default
trapping loads), and two near-miss sources that the selector rejects. -/
namespace Backend.Stock.MemorySinkExt.Fixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open Backend.Stock.Memory.SinkExtend
open Backend.Stock.Memory.ExtendedRoots (Kind)
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.lower

/-- The filetest block: `v1 = load.<in> v0; v2 = <op>.<out> v1; return v2`. -/
def block (kind : Kind) (out : Clif.Ty) : Clif.Block :=
  { id := 0, params := [(0,.i64)],
    body := [⟨[1],.load .load (loadTy kind) {} 0 0⟩,⟨[2],.extend (extendOp kind) out 1⟩],
    term := .ret [2] }

/-- The filetest function with signature `(i64) -> <out>`. -/
def function (kind : Kind) (out : Clif.Ty) : Clif.Function :=
  { name := "load_extend",
    sig := { params := [⟨.i64,.none,.normal⟩], returns := [⟨out,.none,.normal⟩] },
    blocks := [block kind out] }

theorem dominated (kind : Kind) (out : Clif.Ty) : Dominated (function kind out) := by
  constructor
  · change ([0,1,2] : List Nat).Nodup; decide
  · intro ctx ranges st build bi b found
    have bound : bi < 1 := by have h := lt_of_getElem? found; simpa [function] using h
    have zero : bi = 0 := by omega
    subst bi
    simp [function] at found
    subst b
    constructor
    · intro j stm present
      cases j with
      | zero =>
        simp [block] at present
        subst stm
        intro x member
        have zero : x = 0 := by simpa [Driver.instArgs] using member
        subst x
        simp [availOf,function,block,defsBefore,defsFrom]
      | succ j =>
        cases j with
        | zero =>
          simp [block] at present
          subst stm
          intro x member
          have one : x = 1 := by simpa [Driver.instArgs] using member
          subst x
          simp [availOf,function,block,defsBefore,defsFrom]
        | succ j => simp [block] at present
    · intro x member
      have two : x = 2 := by
        simpa [abiTerm,Driver.termArgs,sretRet,sigRets,function,block] using member
      subst x
      simp [availOf,function,block,defsBefore,defsFrom]
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := function kind out) (ctx := ctx) (gn := id)).cand tl x available
    have length : (function kind out).blocks.length = 1 := rfl
    omega

private theorem dominatedB_of_facts {f : Clif.Function}
    (unique : nodupB (valueDefs f) = true) (dominated : Dominated f) : dominatedB f = true := by
  simp only [dominatedB,unique,Bool.true_and]
  cases built : Backend.buildCtx f with
  | error message => rfl
  | ok output =>
    obtain ⟨ctx,ranges,st⟩ := output
    simp only
    apply List.all_eq_true.mpr
    intro bi member
    cases block : f.blocks[bi]? with
    | none => simp only [block]
    | some b =>
      simp only [block,Bool.and_eq_true,List.all_eq_true]
      have facts := ctxFacts_of built
      have defs : DefsAt ctx b (startOnly (blockStart f bi)).start := fun k stm atStatement r contains =>
        (facts.defs dominated.ssa r _).mpr ⟨bi,b,k,stm,block,atStatement,contains,rfl⟩
      refine ⟨⟨?_,?_⟩,?_⟩
      · intro j member
        cases statement : b.body[j]? with
        | none => simp only [statement]
        | some stm =>
          simp only [statement,List.all_eq_true]
          intro y contains
          exact (mem_avail block defs).mp ((dominated.uses _ _ _ built bi b block).1 j stm statement y contains)
      · intro y contains
        exact (mem_avail block defs).mp ((dominated.uses _ _ _ built bi b block).2 y contains)
      · intro x available
        simp only [Bool.or_eq_true,Std.HashSet.contains_ofList,List.contains_iff_mem,
          List.all_eq_true,Bool.not_eq_true',Bool.eq_false_iff,ne_eq]
        by_cases isLocal : x ∈ defsOf f bi
        · exact .inl isLocal
        · exact .inr (dominated.paramFree _ _ _ built bi x available isLocal)

private def effects (kind : Kind) (out : Clif.Ty) : Option Bool :=
  (Stock.lower (function kind out)).toOption.map fun result => Memory.effectsOnly result.code

section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.lower
private theorem scope_uextend : lowerScopeB (function .unsigned8 .i32) = true := by decide +kernel
private theorem scope_sextend : lowerScopeB (function .signed16 .i64) = true := by decide +kernel
private theorem effects_uextend : effects .unsigned8 .i32 = some true := by decide +kernel
private theorem effects_sextend : effects .signed16 .i64 = some true := by decide +kernel
end Kernel

private theorem source_of (kind : Kind) (out : Clif.Ty) (selected : eligible (function kind out) = true)
    (scope : lowerScopeB (function kind out) = true) (abi : sigAbiOk (function kind out).sig = true)
    (registers : Memory.registerEntry (function kind out).sig = true) :
    sourceOk (function kind out) = true := by
  simp only [sourceOk,Bool.and_eq_true,Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨selected,scope⟩,?_⟩,abi⟩,by simp [function,sigRets]⟩,registers⟩
  apply dominatedB_of_facts ?_ (dominated kind out)
  change nodupB [0,1,2] = true
  simp [nodupB]

private theorem check_of (kind : Kind) (out : Clif.Ty) (source : sourceOk (function kind out) = true)
    (effective : effects kind out = some true) :
    ∃ result,Stock.lower (function kind out) = .ok result ∧ check (function kind out) result.code = true := by
  unfold effects at effective
  cases run : Stock.lower (function kind out) with
  | error e => rw [run] at effective; cases effective
  | ok result =>
    rw [run] at effective
    have only : Memory.effectsOnly result.code = true := Option.some.inj effective
    refine ⟨result,rfl,?_⟩
    simp only [check,source,run,Bool.true_and,decide_true,only]

/-- Both filetest functions pass the actual executable source checker and the actual
artifact check, and the source checker derives their proved class. -/
theorem checked_sink_extend_witness :
    sourceOk (function .unsigned8 .i32) = true ∧ sourceOk (function .signed16 .i64) = true ∧
      (∃ kind ty,SinkExtClass kind ty (function .unsigned8 .i32)) ∧
      (∃ kind ty,SinkExtClass kind ty (function .signed16 .i64)) ∧
      (∃ result,Stock.lower (function .unsigned8 .i32) = .ok result ∧
        check (function .unsigned8 .i32) result.code = true) ∧
      (∃ result,Stock.lower (function .signed16 .i64) = .ok result ∧
        check (function .signed16 .i64) result.code = true) := by
  have unsignedSource := source_of .unsigned8 .i32 rfl scope_uextend rfl rfl
  have signedSource := source_of .signed16 .i64 rfl scope_sextend rfl rfl
  exact ⟨unsignedSource,signedSource,sourceOk_sound unsignedSource,sourceOk_sound signedSource,
    check_of .unsigned8 .i32 unsignedSource effects_uextend,
    check_of .signed16 .i64 signedSource effects_sextend⟩

/-- Already-extending loads and extensions of another value keep the previous provider. -/
theorem near_misses_excluded :
    eligible {function .unsigned8 .i32 with blocks := [{block .unsigned8 .i32 with
      body := [⟨[2],.load .uload8 .i32 {} 0 0⟩]}]} = false ∧
    eligible {function .unsigned8 .i32 with blocks := [{block .unsigned8 .i32 with
      body := [⟨[1],.load .load .i8 {} 0 0⟩,⟨[2],.extend .uextend .i32 0⟩]}]} = false := by
  exact ⟨rfl,rfl⟩

end Backend.Stock.MemorySinkExt.Fixture
