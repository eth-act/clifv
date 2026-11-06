import FV.Backend.Proof.StockMemorySinkExtBody
import FV.Backend.Proof.StockMemoryNotrap
import FV.Backend.Proof.StockMemoryContract
import FV.E2E.Statement

/-! The source contract of memory families whose loads may trap. `Stock.Memory.Domain`
asks for a VCode trap for every source trap, which a faulting load cannot give: the
VCode has no memory-access traps. The run premise `TrapsExplicit` of the E2E theorems
already excludes memory-access traps (as for the legacy route), so this contract asks
for the trap refinement only on runs whose traps are explicit.

The sinking load/extension class satisfies it vacuously: under `TrapsExplicit` its
source run never traps. The load cannot trap (it is not an explicit trap) and the
extension and return never trap. No statement about the machine's behaviour on a
faulting address is needed: neither "the extending load traps exactly when the plain
load traps" nor its converse is used. -/
namespace Backend.Stock.Memory
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open Backend.Stock.Memory.ExtendedRoots (Kind)
set_option autoImplicit false
set_option Elab.async false

/-- The memory contract with traps required only under explicit-trap runs. -/
structure ExplicitDomain (f : Clif.Function) : Prop where
  scope : LowerScope f
  dominated : Dominated f
  abi : sigAbiOk f.sig = true
  ordinary : (sigRets f.sig).any (·.purpose == .sret) = false
  returns : ∀ {result : Stock.Result} (run : Stock.lower f = .ok result)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals mem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    (memoryOk : MemRelOk F sb syms f MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w),
    ∃ ρ, RunOkABI f result.code isem MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals mem)
  traps : ∀ {result : Stock.Result} (run : Stock.lower f = .ok result)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {code : Clif.TrapCode}
    (explicit : E2E.TrapsExplicit env cp ⟨fr,[],cm⟩)
    (trapped : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .trapped code)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    (memoryOk : MemRelOk F sb syms f MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w),
    ∃ ρ, VTrapFrom result.code isem ⟨0,0,ρ,w⟩ code

/-- Every existing memory domain is an explicit-trap domain. -/
theorem ExplicitDomain.of_domain {f : Clif.Function} (domain : Domain f) : ExplicitDomain f := by
  refine ⟨domain.scope,domain.dominated,domain.abi,domain.ordinary,domain.returns,?_⟩
  intro result run args cm fr entered env cp fuel code _ trapped
  exact domain.traps run entered trapped

end Backend.Stock.Memory

namespace Backend.Stock.Memory.SinkExtend
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open Backend.Stock.Memory.ExtendedRoots (Kind)
set_option autoImplicit false
set_option Elab.async false

/-- The production source class: original syntax and the original scope, dominance
and ABI conditions. No run or output artifact is part of this predicate. -/
structure SinkExtClass (kind : Kind) (ty : Clif.Ty) (f : Clif.Function) : Prop where
  scope : LowerScope f
  dominated : Dominated f
  abi : sigAbiOk f.sig = true
  ordinary : (sigRets f.sig).any (·.purpose == .sret) = false
  registers : ∀ loc ∈ locsOf f.sig,∃ pin,loc = .reg pin
  shape : ∃ (b : Clif.Block) (x y z : Nat) (flags : Clif.MemFlags),Shape kind f b x y z ty flags

/-- An extension never traps. -/
theorem extend_notrap (fr : Clif.Frame) (cm : Clif.Mem) (op : Clif.ExtendOp) (ty : Clif.Ty) (y : Nat)
    (code : Clif.TrapCode) : Clif.evalInst fr cm (.extend op ty y) ≠ .trap code := by
  intro trapped
  simp only [Clif.evalInst] at trapped
  cases got : fr.get y with
  | trap c => exact fr.get_ne_trap y c got
  | stuck m => rw [got] at trapped; cases trapped
  | ok a =>
    rw [got] at trapped
    simp only [Clif.Res.ok_bind] at trapped
    by_cases wide : a.ty.width < ty.width
    · simp only [wide,decide_true,Clif.Res.check_true,Clif.Res.ok_bind] at trapped
      cases op <;> cases trapped
    · simp only [wide,decide_false,Clif.Res.check_false,Clif.Res.stuck_bind] at trapped
      cases trapped

/-- Under explicit traps the original source run of the class never traps: the load
is not an explicit trap, and the extension and the return cannot trap. -/
theorem stock_sink_extend_no_trap (kind : Kind) {f : Clif.Function} {b : Clif.Block}
    {x y z : Nat} {ty : Clif.Ty} {flags : Clif.MemFlags} (shape : Shape kind f b x y z ty flags)
    {fr : Clif.Frame} {cm : Clif.Mem} (body : fr.body = b.body) (term : fr.term = b.term)
    {env : Clif.Env} {cp : Clif.Program} (explicit : E2E.TrapsExplicit env cp ⟨fr,[],cm⟩)
    (fuel : Nat) (code : Clif.TrapCode) :
    Clif.runLoop env cp fuel ⟨fr,[],cm⟩ ≠ .trapped code := by
  cases fuel with
  | zero => simp
  | succ fuel =>
    rw [Clif.runLoop_succ]
    have first : (⟨fr,[],cm⟩ : Clif.State).frame.body =
        ⟨[y],.load .load (loadTy kind) flags x 0⟩ :: [⟨[z],.extend (extendOp kind) ty y⟩] := by
      change fr.body = _
      rw [body,shape.body]
    rw [Clif.step_inst env cp _ _ _ first (by intro fn args impossible; cases impossible)
      (by intro sig callee args impossible; cases impossible)]
    cases evaluated : Clif.evalInst fr cm (.load .load (loadTy kind) flags x 0) with
    | trap c =>
      have stepped : Clif.step env cp ⟨fr,[],cm⟩ = .trapped c := by
        rw [Clif.step_inst env cp _ _ _ first (by intro fn args impossible; cases impossible)
          (by intro sig callee args impossible; cases impossible)]
        change Clif.StepResult.ofRes (Clif.evalInst fr cm _) _ = _
        rw [evaluated]
        rfl
      have impossible := explicit.stmt ⟨fr,[],cm⟩ c _ _ (.refl _) stepped first
      cases impossible
    | stuck message =>
      simp [Clif.StepResult.ofRes]
    | ok pair =>
      obtain ⟨vals,cm'⟩ := pair
      simp only [Clif.StepResult.ofRes,Clif.continueWith]
      cases written : fr.regs.setMany [y] vals with
      | none => simp
      | some regs =>
        simp only
        apply OrdinaryBody.ordinary_source_notrap fuel _ rfl ?_ (xs := [z]) (by change fr.term = _; rw [term,shape.ret])
        intro stm member
        simp only [List.mem_singleton] at member
        subst stm
        constructor
        · constructor
          · intro fn args impossible; cases impossible
          · intro sig callee args impossible; cases impossible
        · intro fr cm c
          exact extend_notrap fr cm _ ty y c

/-- The class derives the explicit-trap memory contract: returns from the sinking body,
traps vacuously from `stock_sink_extend_no_trap`. -/
theorem SinkExtClass.domain {kind : Kind} {ty : Clif.Ty} {f : Clif.Function}
    (family : SinkExtClass kind ty f) : ExplicitDomain f := by
  obtain ⟨b,x,y,z,flags,shape⟩ := family.shape
  refine ⟨family.scope,family.dominated,family.abi,family.ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable memoryOk w memory arguments
    exact stock_sink_extend_returns kind run family.scope family.dominated family.abi shape entered
      returned refines driver memorySem stable memoryOk memory arguments
  · intro result run args cm fr entered env cp fuel code explicit trapped
    obtain ⟨b',regs,entry,_,_,_,frame⟩ := entered
    have same : b' = b := by
      have found : some b = some b' := by
        simpa only [Clif.Function.entry?,shape.blocks,List.head?_cons] using entry
      exact Option.some.inj found.symm
    subst b'
    have body : fr.body = b.body := by rw [frame]
    have term : fr.term = b.term := by rw [frame]
    exfalso
    exact (stock_sink_extend_no_trap kind shape body term explicit fuel code trapped)

end Backend.Stock.Memory.SinkExtend
