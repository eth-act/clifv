import Crates.CompileExeSourceWitness
import Crates.FrontendBundleInput
import FV.Link.NonVacuityDeadCleanupExeSource
import FV.Front.Exe

/-! # Non-vacuity of the frontend bundle's theorems on a real codegen unit (T7d, T7e)

The bundle `bw` holds the codegen unit of the survey crate `g_u128` (`Crates.FrontendBundleInput`,
as `cargo fv link-proof` collected it) restricted to two of its functions, cg_clif's dumps of
them decoded in Lean (`Front.parseUnit`): `wmul_u128` (a global symbol) and its callee
`core::num::<u128>::wrapping_mul`, a **local** symbol of the unit (CLIF name
`_RNvMs8_…wrapping_mul`, which the object merge linked as `__fv_cc1bb1bbc108__RNvMs8_…wrapping_mul`).
`wmul_u128`'s Lean code is at 16 MiB (the merge's marker), the sizes are the cleanup pipeline's.
`Crates.FrontendBundleWitnessRaw`: the same run as cg_clif's program, before the decoding.

* `buildSpec_eq`: `Front.buildSpec bw = .ok S`; `compile_eq`: the shipped compiler
  (`Link.DeadCleanup.compileExe`) compiles `S` into the placeholder executable of
  `Crates.LeanLinkWitness`.
* The scoping `sc` (every name as the frontend wrote it) is a scoping of the units
  (`sc_ok`), as are the linked names (`fin_ok`); `Front.link_alpha` relates the two programs by a
  bijection `σ` (`alpha`), which moves `wrapping_mul`'s CLIF name to its linked name
  (`renamed`: the CLIF name is a function of the pre-renaming program, not of the linked one,
  and conversely).
* **`bundle_source_witness`**: `Front.bundle_correct_source` instantiated, all premises
  discharged, with the outside world `Link.SourceWitness.helperBase` (its CLIF environment
  renamed back by `σ`) and the pre-renaming entry state of `wmul_u128` on `2^64 + 3` and `5`: the
  pre-renaming program's CLIF run returns `5 * 2^64 + 15`, and the executable machine, called
  with the split arguments `3, 1, 5, 0` in x0–x3, returns to the caller with `15, 5` in x0, x1.
* `data_witness`: the whole unit parses, and the object `c_Ldata4`, which no function names but
  the root `c_Ldata3` relocates to, is in its data closure (`Front.data_complete`, `Reach.ref`).
-/

namespace Crates.FrontendBundleWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Opt.Legalize128
open Link (LinkSpec inScopePar_eq)
open Link.SourceWitness (helperEnv helperBase)
open Crates.BinaryWitness (memOf)
open Crates.CompileExeSourceWitness (n args args' M sp0 ra0 sp0_toNat)
open Crates.FrontendBundleInput (fn26 fn2 unitWith symbols fns)

/-! ## The bundle and its `LinkSpec` -/

/-- The bundle without the sizes: the unit with `wmul_u128` and `wrapping_mul`, the executable's
symbols, `wmul_u128`'s Lean code at 16 MiB. -/
def b0 : Front.Bundle :=
  { units := [unitWith [fn26, fn2]], symbols, markers := [("wmul_u128", 0x1000000)], sizes := [] }

/-- The cleanup pipeline's sizes of the assembled (renamed) functions, by linked name. -/
def sizes0 : List (String × Nat) :=
  match Front.assemble b0 with
  | .ok A => A.names.zip (A.funcs.map fun fi =>
      (getOk (pipeCleanupT fi.func fi.k 0 (raJ fi.ra fi.j))).fb.words.size)
  | .error _ => []

/-- **The bundle.** -/
def bw : Front.Bundle := { b0 with sizes := sizes0 }

theorem buildSpec_ok : (Front.buildSpec bw).toBool = true := by native_decide

/-- The `LinkSpec` built from the bundle. -/
def S : LinkSpec := getOk (Front.buildSpec bw)

theorem buildSpec_eq : Front.buildSpec bw = .ok S := getOk_eq buildSpec_ok

/-- The executable before the compiler: the region's placeholder, the link map's symbols. -/
def file0 : ByteArray :=
  LeanLinkWitness.placeholder S.R S.size (S.addrs.map fun p => (BinCheck.symName p.1, p.2))

theorem link_ok : (Link.DeadCleanup.leanLink S file0).toBool = true := by native_decide

/-- The executable. -/
def file : ByteArray := getOk (Link.DeadCleanup.leanLink S file0)

theorem link_eq : Link.DeadCleanup.leanLink S file0 = .ok file := getOk_eq link_ok

theorem inScope : InScopeP S.input0 = true := by native_decide

/-- **The shipped executable compiler compiles the bundle's `LinkSpec` to `file`.** -/
theorem compile_eq : Link.DeadCleanup.compileExe S file0 = .ok file := by
  simp only [Link.DeadCleanup.compileExe, inScopePar_eq, inScope, ↓reduceIte, link_eq]

/-! ## The units, the scopings, the renaming -/

theorem units_ok : (bw.units.mapM Front.parseUnit).toBool = true := by native_decide

/-- The parsed units. -/
def us : List Front.PCgu := getOk (bw.units.mapM Front.parseUnit)

theorem hus : bw.units.mapM Front.parseUnit = .ok us := getOk_eq units_ok

/-- The parsed unit. -/
def u0 : Front.PCgu := us.headD default

theorem us_len : us.length = 1 := by native_decide

theorem us0 : us[0]? = some u0 := by
  unfold u0
  have h := us_len
  cases hc : us with
  | nil => rw [hc] at h; cases h
  | cons a l => rfl

/-- **The pre-renaming scoping**: every name as the frontend wrote it. -/
def sc : Nat → String → String := fun _ x => x

theorem sc_ok : Front.ScopingOk us sc := Front.scopingDecB_sound (by native_decide)

theorem fin_ok : Front.ScopingOk us (Front.finOf us) := by
  obtain ⟨us', hus', hsc, -⟩ := Front.buildSpec_spec buildSpec_eq
  rw [hus] at hus'
  cases hus'
  exact hsc

/-- `wrapping_mul`'s CLIF name (a local symbol of the unit). -/
def mulClif : String := fn2.name

/-- `wrapping_mul`'s linked name. -/
def mulLinked : String := "__fv_cc1bb1bbc108__RNvMs8_NtCsazjiGSRkgVH_4core3numo12wrapping_mul"

/-- The two programs differ: the pre-renaming one names `wrapping_mul` by its CLIF name, the
linked one by its linked name. -/
theorem renamed :
    ((Front.link us sc).func? mulClif).isSome = true ∧ (Front.link us sc).func? mulLinked = none ∧
    ((Front.link us (Front.finOf us)).func? mulLinked).isSome = true ∧
    (Front.link us (Front.finOf us)).func? mulClif = none ∧
    Front.finOf us 0 mulClif = mulLinked ∧ Front.finOf us 0 n = n := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

theorem idents : n ∈ u0.idents ∧ mulClif ∈ u0.idents := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- **The alpha-equivalence of the two programs** (`Front.link_alpha`): a bijection `σ` with the
linked program the pre-renaming one renamed, keeping `wmul_u128`, moving `wrapping_mul`'s CLIF
name to its linked name. -/
theorem alpha : ∃ σ : Clif.Ren,
    Front.link us (Front.finOf us) = (Front.link us sc).rename σ.fwd ∧
    σ.fwd n = n ∧ σ.fwd mulClif = mulLinked := by
  obtain ⟨σ, hσ, hl, -⟩ := Front.link_alpha sc_ok fin_ok
  refine ⟨σ, hl, ?_, ?_⟩
  · have := hσ 0 u0 n us0 idents.1
    rw [renamed.2.2.2.2.2] at this
    exact this
  · have := hσ 0 u0 mulClif us0 idents.2
    rw [renamed.2.2.2.2.1] at this
    exact this

/-- The source program of a `LinkSpec` built from a bundle of the units `us` is the
pre-renaming program renamed. -/
theorem srcProg_of {b : Front.Bundle} {S' : LinkSpec} (hb : Front.buildSpec b = .ok S')
    (hu : b.units.mapM Front.parseUnit = .ok us) {σ : Clif.Ren}
    (hσ : Front.link us (Front.finOf us) = (Front.link us sc).rename σ.fwd) :
    S'.input0.srcProg = (Front.link us sc).rename σ.fwd := by
  obtain ⟨us', hus', -, hs⟩ := Front.buildSpec_srcProg hb
  rw [hu] at hus'
  cases hus'
  rw [← hσ, ← hs]

theorem srcProg_eq {σ : Clif.Ren}
    (hσ : Front.link us (Front.finOf us) = (Front.link us sc).rename σ.fwd) :
    S.inputCleanup.srcProg = (Front.link us sc).rename σ.fwd :=
  srcProg_of buildSpec_eq hus hσ

/-- `wmul_u128` of the pre-renaming program. -/
def f0 : Clif.Function := ((Front.link us sc).func? n).getD default

theorem hf0 : (Front.link us sc).func? n = some f0 := by native_decide

theorem f0_mentions : mentions128 f0 = true := by native_decide

theorem link_data : (Front.link us sc).data = [] := rfl

/-- Renaming there and back. -/
theorem fn_back (σ : Clif.Ren) (g : Clif.Function) : (g.rename σ.fwd).rename σ.bwd = g := by
  rw [Front.Function.rename_rename]
  simp only [σ.bwd_fwd]
  exact Front.Function.rename_id' g

theorem prog_back (σ : Clif.Ren) (p : Clif.Program) (hd : p.data = []) :
    (p.rename σ.fwd).rename σ.bwd = p := by
  cases p with
  | mk hdr data funcs =>
    simp only at hd
    subst hd
    simp only [Clif.Program.rename, List.map_nil, List.map_map, Function.comp_def, fn_back,
      List.map_id']

/-! ## From the linked program back to the pre-renaming one -/

section Back

variable {σ : Clif.Ren} {P : Clif.Program} (hP : P = (Front.link us sc).rename σ.fwd)
include hP

/-- The linked `wmul_u128` is the pre-renaming one renamed. -/
theorem pre_fn (hσn : σ.fwd n = n) {g : Clif.Function} (hg : P.func? n = some g) :
    f0.rename σ.fwd = g := by
  have h1 : P.func? (σ.fwd n) = some (f0.rename σ.fwd) := by
    rw [hP, Clif.Program.rename_func?, hf0]; rfl
  rw [hσn, hg] at h1
  exact (Option.some.inj h1).symm

theorem pre_back : P.rename σ.symm.fwd = Front.link us sc := by
  rw [hP, Clif.Ren.symm_fwd, prog_back σ _ link_data]

/-- The source memory bound, renamed back. -/
theorem pre_bnd {s : Clif.State}
    (h : ∀ s', Opt.Legal.SReach helperEnv P s s' → Opt.Legal.MemBounded s'.mem) :
    ∀ s', Opt.Legal.SReach (helperEnv.ren σ.symm) (Front.link us sc) (s.ren σ.symm) s' →
      Opt.Legal.MemBounded s'.mem := by
  have := Front.bnd_ren (σ := σ.symm) h
  rwa [pre_back hP] at this

/-- The call-depth bound, renamed back. -/
theorem pre_depth {s : Clif.State} {d : Nat} (h : Clif.DepthLe helperEnv P d s) :
    Clif.DepthLe (helperEnv.ren σ.symm) (Front.link us sc) d (s.ren σ.symm) := by
  have := Front.depthLe_ren (σ := σ.symm) h
  rwa [pre_back hP] at this

/-- A return of the linked program's run is a return of the pre-renaming program's run. -/
theorem pre_run {s : Clif.State} {k : Nat} {vals : List Clif.Val} {m : Clif.Mem}
    (h : Clif.runLoop helperEnv P k s = .returned vals m) :
    Clif.runLoop (helperEnv.ren σ.symm) (Front.link us sc) k (s.ren σ.symm) =
      .returned vals (m.ren σ.symm) := by
  have h1 : Clif.runLoop ((helperEnv.ren σ.symm).ren σ) ((Front.link us sc).rename σ.fwd) k
      ((s.ren σ.symm).ren σ) = .returned vals m := by
    rw [Front.Env.ren_symm_ren, ← hP, Front.State.ren_symm_ren]
    exact h
  obtain ⟨m0, h0, hmr⟩ := Clif.runLoop_ren_returned_inv σ _ _ k _ h1
  rw [h0, hmr, Clif.Mem.ren_ren_symm]

end Back

/-- The linked entry, renamed back. -/
theorem pre_entry {σ : Clif.Ren} {g : Clif.Function} {a : List Clif.Val} {s : Clif.State}
    (hfs : f0.rename σ.fwd = g) (h : ClifEntry g a s) : ClifEntry f0 a (s.ren σ.symm) := by
  have := Front.clifEntry_ren (σ := σ.symm) h
  rwa [Clif.Ren.symm_fwd, ← hfs, fn_back] at this

/-- The split result `15, 5` of `5 * 2^64 + 15`. -/
theorem split_ret {vals' : List Clif.Val}
    (h : Opt.Legal.ExpRel [[.lo, .hi]] [⟨.i128, 5#64 ++ 15#64⟩] vals') :
    vals' = [⟨.i64, 15#64⟩, ⟨.i64, 5#64⟩] := by
  obtain ⟨a, b, rest, rfl, ⟨l, hh', e1, rfl, rfl⟩, hrest⟩ : ∃ a b rest, vals' = a :: b :: rest ∧
      Opt.Legal.Halves ⟨.i128, 5#64 ++ 15#64⟩ a b ∧ Opt.Legal.ExpRel [] [] rest := by
    match vals', h with
    | a :: b :: rest, ⟨hv, hr⟩ => exact ⟨a, b, rest, rfl, hv, hr⟩
  cases rest with
  | cons => exact absurd hrest id
  | nil =>
    obtain ⟨-, e1⟩ := Clif.Val.mk.inj e1
    have hl : l = 15#64 := by
      have := congrArg (fun x : BitVec 128 => x.extractLsb' 0 64) (eq_of_heq e1)
      have h2 : (hh' ++ l).extractLsb' 0 64 = 15#64 := by simpa using this.symm
      exact (BitVec.extractLsb'_append_eq_right (a := hh')).symm.trans h2
    have hh2 : hh' = 5#64 := by
      have := congrArg (fun x : BitVec 128 => x.extractLsb' 64 64) (eq_of_heq e1)
      have h2 : (hh' ++ l).extractLsb' 64 64 = 5#64 := by simpa using this.symm
      exact (BitVec.extractLsb'_append_eq_left (b := l)).symm.trans h2
    subst hl hh2
    rfl

/-! ## The compiler's input: the facts of `Crates.DeadCleanupExeSourceWitness`, for `S` -/

/-- The cleanup input. -/
abbrev J : LinkInput := S.inputCleanup

/-- The **source** `wmul_u128` (as parsed, with `i128` parameters and result). -/
def fs : Clif.Function := (J.srcProg.func? n).getD default

/-- The compiled function: its legalisation. -/
def f : Clif.Function := ((prog J).func? n).getD default

def bS : Clif.Block := fs.entry?.getD default
def bF : Clif.Block := f.entry?.getD default

/-- The body's stack pointer of the entry. -/
def sb : BitVec 64 := sp0 - BitVec.ofNat 64 (frameDrop (artOf J.resultsCleanup f).af)

/-- The caller's CLIF memory: no live allocation, the CLIF image's symbols, the slot-placement
oracle at the entry's body `sp`. -/
def cm : Clif.Mem :=
  { symbols := fun n => J.syms.lookup n, place := some ⟨[sb], (sys J helperBase).frames, none⟩ }

/-- The source entry state of `wmul_u128` on the two `i128` values (linked names). -/
def cs : Clif.State where
  frame := { func := fs, regs := (Clif.Regs.empty.setMany (bS.params.map (·.1)) args).getD default,
             slots := [], body := bS.body, term := bS.term }
  callers := []
  mem := cm

/-- The target entry state of the legalised `wmul_u128` on the split arguments. -/
def cs' : Clif.State where
  frame := { func := f, regs := (Clif.Regs.empty.setMany (bF.params.map (·.1)) args').getD default,
             slots := [], body := bF.body, term := bF.term }
  callers := []
  mem := cm

/-- The linked program's CLIF run from `cs`. -/
def run : Clif.Outcome := Clif.runLoop helperEnv J.srcProg M cs

/-- The machine state of the call with memory `m`: pc at `f`'s address, x30 the caller's return
address, `sp0`, the split arguments in x0–x3. -/
def r (m : Arm.Memory) : Arm.ArmState :=
  Arm.w .PC (artOf J.resultsCleanup f).base (Arm.w (.GPR 30#5) ra0 (Arm.w (.GPR 31#5) sp0
    (Arm.w (.GPR 0#5) 3#64 (Arm.w (.GPR 1#5) 1#64 (Arm.w (.GPR 2#5) 5#64
      (Arm.w (.GPR 3#5) 0#64 (setMem Arm.ArmState.default m)))))))

def gpB : Bool :=
  match Opt.Legal.groups fs.sig.params with
  | some [[.lo, .hi], [.lo, .hi]] => true
  | _ => false

def grB : Bool :=
  match Opt.Legal.groups fs.sig.returns with
  | some [[.lo, .hi]] => true
  | _ => false

def locB : Bool :=
  match locsOf f.sig with
  | [.reg (.x 0), .reg (.x 1), .reg (.x 2), .reg (.x 3)] => true
  | _ => false

/-- The facts decided on the source and the compiled program. -/
def factsB : Bool :=
  decide (J.srcProg.func? n = some fs) && decide ((prog J).func? n = some f) &&
  decide (legalize fs = f) && mentions128 fs &&
  decide (fs.entry? = some bS) && decide (f.entry? = some bF) &&
  decide (args.map (·.ty) = fs.sig.params.map (·.ty)) &&
  decide (bS.params.map (·.2) = args.map (·.ty)) &&
  (Clif.Regs.empty.setMany (bS.params.map (·.1)) args).isSome &&
  decide (args'.map (·.ty) = f.sig.params.map (·.ty)) &&
  decide (bF.params.map (·.2) = args'.map (·.ty)) &&
  (Clif.Regs.empty.setMany (bF.params.map (·.1)) args').isSome &&
  decide (fs.slots = []) && decide (f.slots = []) && locB &&
  gpB && grB &&
  LinkWitness.isRet run && decide (LinkWitness.retVals run = [⟨.i128, 5#64 ++ 15#64⟩]) &&
  (tabOf J.resultsCleanup).all
    (fun e => decide (e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32)) &&
  DeadCleanupStackBound.goodN J n &&
  decide (DeadCleanupStackBound.stackFn J (legalize fs) ≤ 2 ^ 20) &&
  (prog J).funcs.all (fun g => !Backend.hasTls g) &&
  (prog J).funcs.all (fun g => g.externs.all fun e =>
    ((prog J).func? e.2.name).isSome || !Clif.Rust.isDivHelper e.2.name) &&
  (prog J).funcs.all indFreeB && (prog J).funcs.all (fun g => (indSigs g).isEmpty) &&
  J.srcProg.funcs.all (fun g => g.slots.isEmpty) && SrcScopeB J

theorem factsB_true : factsB = true := by native_decide

theorem facts :
    J.srcProg.func? n = some fs ∧ (prog J).func? n = some f ∧ legalize fs = f ∧
    mentions128 fs = true ∧ fs.entry? = some bS ∧ f.entry? = some bF ∧
    args.map (·.ty) = fs.sig.params.map (·.ty) ∧ bS.params.map (·.2) = args.map (·.ty) ∧
    (Clif.Regs.empty.setMany (bS.params.map (·.1)) args).isSome = true ∧
    args'.map (·.ty) = f.sig.params.map (·.ty) ∧ bF.params.map (·.2) = args'.map (·.ty) ∧
    (Clif.Regs.empty.setMany (bF.params.map (·.1)) args').isSome = true ∧
    fs.slots = [] ∧ f.slots = [] ∧ locB = true ∧
    gpB = true ∧ grB = true ∧
    LinkWitness.isRet run = true ∧ LinkWitness.retVals run = [⟨.i128, 5#64 ++ 15#64⟩] ∧
    (tabOf J.resultsCleanup).all
      (fun e => decide (e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32)) = true ∧
    DeadCleanupStackBound.goodN J n = true ∧
    DeadCleanupStackBound.stackFn J (legalize fs) ≤ 2 ^ 20 ∧
    (prog J).funcs.all (fun g => !Backend.hasTls g) = true ∧
    (prog J).funcs.all (fun g => g.externs.all fun e =>
      ((prog J).func? e.2.name).isSome || !Clif.Rust.isDivHelper e.2.name) = true ∧
    (prog J).funcs.all indFreeB = true ∧ (prog J).funcs.all (fun g => (indSigs g).isEmpty) = true ∧
    J.srcProg.funcs.all (fun g => g.slots.isEmpty) = true ∧ SrcScopeB J = true := by
  have h := factsB_true
  simp only [factsB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩,
    h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩, h24⟩, h25⟩, h26⟩, h27⟩,
    h28⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26, h27, h28⟩

/-- `okBCleanup` of the cleanup input (by construction, `Link.DeadCleanup.okB_leanLink`). -/
theorem okB_J : okBCleanup J = true :=
  Link.DeadCleanup.okB_leanLink (by rw [Link.DeadCleanup.inScope_input]; exact inScope) link_eq

/-- No call cycle of the program's call graph is reachable from the entry. -/
theorem acyclic : ¬ DeadCleanupStackBound.CycleFrom
    (DeadCleanupStackBound.Calls J J.resultsCleanup) (legalize fs) := by
  obtain ⟨f', hf', hc⟩ := (DeadCleanupStackBound.goodN_iff okB_J).1
    facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [facts.2.1] at hf'
  cases hf'
  rw [facts.2.2.1]
  exact hc

/-- Every code address of the program is below `2^32`. -/
theorem img_lt {x : BitVec 64} (h : img J x) : x.toNat < 2 ^ 32 := by
  obtain ⟨e, he, p, hp, hx⟩ := h
  have hb' : e.2.base.toNat + 4 * e.2.fb.words.size + 4 ≤ 2 ^ 32 := by
    have := List.all_eq_true.mp facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e he
    simpa using this
  obtain ⟨j, hj, e'⟩ := LinkWitness.wordsAt_mem_inv (k := 0) hp
  simp only [Array.length_toList] at hj
  rw [e', BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at hx
  have := e.2.base.isLt
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega : 4 * (0 + j) < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : e.2.base.toNat + 4 * (0 + j) < 2 ^ 64)] at hx
  omega

section State

variable (m : Arm.Memory)

theorem pc_r : Arm.r .PC (r m) = (artOf J.resultsCleanup f).base := Arm.r_of_w_same

theorem spv_r : spv (r m) = sp0 := by
  simp only [spv, r]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide), Arm.r_of_w_same]

theorem x30_r : xreg 30 (r m) = ra0 := by
  simp only [xreg, r]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_same]

theorem err_r : Arm.r .ERR (r m) = .None := by
  simp only [r]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), r_setMem]
  simp [Arm.r, Arm.read_base_error, Arm.ArmState.default]

theorem x0_r : Arm.r (.GPR (rnum 0)) (r m) = 3#64 := by
  simp only [r, rnum]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_same]

theorem x1_r : Arm.r (.GPR (rnum 1)) (r m) = 1#64 := by
  simp only [r, rnum]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide), Arm.r_of_w_same]

theorem x2_r : Arm.r (.GPR (rnum 2)) (r m) = 5#64 := by
  simp only [r, rnum]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_same]

theorem x3_r : Arm.r (.GPR (rnum 3)) (r m) = 0#64 := by
  simp only [r, rnum]
  rw [Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide),
    Arm.r_of_w_different (by decide), Arm.r_of_w_different (by decide), Arm.r_of_w_same]

omit m in
theorem locs : locsOf f.sig = [.reg (.x 0), .reg (.x 1), .reg (.x 2), .reg (.x 3)] := by
  have h := facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold locB at h
  split at h
  · assumption
  · cases h

omit m in
theorem gp : Opt.Legal.groups fs.sig.params = some [[.lo, .hi], [.lo, .hi]] := by
  have h := facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold gpB at h
  split at h
  · assumption
  · cases h

omit m in
theorem gr : Opt.Legal.groups fs.sig.returns = some [[.lo, .hi]] := by
  have h := facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold grB at h
  split at h
  · assumption
  · cases h

/-- The outside caller's contract for the legalised `wmul_u128` in `r m` (the split arguments in
x0–x3) with a stack of `N ≤ 2^20` bytes. -/
theorem outsideCall (roB : BitVec 64 → Option (BitVec 8)) {N : Nat} (hN : N ≤ 2 ^ 20) :
    OutsideCall J roB (legalize fs) N (r m) args' cs'.mem where
  pc := by rw [facts.2.2.1]; exact pc_r m
  err := err_r m
  ra := fun h => by have := img_lt h; rw [x30_r] at this; simp [ra0] at this
  spAligned := by rw [spv_r]; decide
  stack := by rw [spv_r, sp0_toNat]; omega
  stackFree := fun a ha hb => by
    have := img_lt ha
    rw [spv_r] at hb
    obtain ⟨-, h2⟩ := hb
    rw [sp0_toNat] at h2
    omega
  args := fun loc v hm => by
    rw [facts.2.2.1, locs] at hm
    simp only [args', List.zip_cons_cons, List.zip_nil_right, List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [VHolds, regVal, x0_r m]; rfl
    · simp only [VHolds, regVal, x1_r m]; rfl
    · simp only [VHolds, regVal, x2_r m]; rfl
    · simp only [VHolds, regVal, x3_r m]; rfl
  bytes := fun _ _ hv => by simp [cs', cm, Clif.Mem.valid] at hv
  image := fun _ _ _ hv => by simp [cs', cm, Clif.Mem.valid] at hv
  valid := fun _ _ hv => by simp [cs', cm, Clif.Mem.valid] at hv
  symbols := rfl

omit m in
theorem clifEntry' : ClifEntry (legalize fs) args' cs' := by
  obtain ⟨-, -, hl, -, -, hb, -, -, -, hsig, hpar, hset, -, hsl, -⟩ := facts
  rw [hl]
  refine ⟨rfl, rfl, hsig, ⟨bF, hb, rfl, rfl, hpar, ?_⟩, by simp [cs', hsl]⟩
  show _ = some ((Clif.Regs.empty.setMany (bF.params.map (·.1)) args').getD default)
  revert hset
  cases Clif.Regs.empty.setMany (bF.params.map (·.1)) args' <;> simp

omit m in
theorem clifEntry : ClifEntry fs args cs := by
  obtain ⟨-, -, -, -, hb, -, hsig, hpar, hset, -, -, -, hsl, -⟩ := facts
  refine ⟨rfl, rfl, hsig, ⟨bS, hb, rfl, rfl, hpar, ?_⟩, by simp [cs, hsl]⟩
  show _ = some ((Clif.Regs.empty.setMany (bS.params.map (·.1)) args).getD default)
  revert hset
  cases Clif.Regs.empty.setMany (bS.params.map (·.1)) args <;> simp

/-- The target entry for `compileExe_correct`. -/
theorem clifRun : ClifRun J helperBase (legalize fs) (r m) args' cs' where
  entry := clifEntry'
  slots := fun _ _ h => by simp [cs'] at h
  place := fun _ => ⟨[], by
    show some _ = some _
    rw [show spBody (art J (legalize fs)).af (r m) = sb by
      simp only [spBody, spv_r, sb, facts.2.2.1]]⟩

end State

/-- The machine's memory is the loaded image of any file. -/
theorem intact (file : ByteArray) : (imageOf file).Intact (r (memOf file)) := fun a b _ hb => by
  simp only [r, LinkWitness.mem_w, mem_setMem, memOf]
  exact (congrArg (Option.getD · 0) hb).trans rfl

/-- The linked program's CLIF run of `wmul_u128` returns `5 * 2^64 + 15`. -/
theorem run_eq : run = .returned [⟨.i128, 5#64 ++ 15#64⟩] (LinkWitness.retMem run) := by
  rw [← facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  exact LinkWitness.eq_returned facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cm_bounded : Opt.Legal.MemBounded cs.mem := fun _ _ h => by
  simp [cs, cm, Clif.Mem.valid] at h

/-! ## The bundle theorem on the pre-renaming program -/

/-- **Per-run non-vacuity of `Front.bundle_correct_source`** on the real codegen unit of
`g_u128` (functions `wmul_u128` and the local `wrapping_mul`): `lean-link`'s `LinkSpec` is built
from the bundle in Lean, the shipped compiler produces the executable `file`; the linked program
is the pre-renaming program (the names as the frontend wrote them) renamed by a bijection `σ`
moving `wrapping_mul`'s CLIF name to its linked name; the **pre-renaming** program's CLIF run of
`wmul_u128` on `2^64 + 3` and `5` (in the outside world `helperBase` renamed back) returns
`5 * 2^64 + 15`; and, the outside code calling the executable's compiled `wmul_u128` with the
split arguments in x0–x3, the executable machine returns to the caller with the split result
`15, 5` in x0, x1. -/
theorem bundle_source_witness :
    Front.buildSpec bw = .ok S ∧ Link.DeadCleanup.compileExe S file0 = .ok file ∧
    bw.units.mapM Front.parseUnit = .ok us ∧ Front.ScopingOk us sc ∧
    (Front.link us sc).func? n = some f0 ∧ mentions128 f0 = true ∧
    ∃ σ : Clif.Ren,
      Front.link us (Front.finOf us) = (Front.link us sc).rename σ.fwd ∧
      σ.fwd mulClif = mulLinked ∧
      Clif.runLoop (helperEnv.ren σ.symm) (Front.link us sc) M (cs.ren σ.symm) =
        .returned [⟨.i128, 5#64 ++ 15#64⟩] ((LinkWitness.retMem run).ren σ.symm) ∧
      ∃ k, ArmRet ra0 (r (memOf file)) (runX (step J helperBase file) k (r (memOf file))) ∧
        XHolds ⟨.i64, 15#64⟩ (xreg 0 (runX (step J helperBase file) k (r (memOf file)))) ∧
        XHolds ⟨.i64, 5#64⟩ (xreg 1 (runX (step J helperBase file) k (r (memOf file)))) := by
  obtain ⟨hf, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hst, htls, hdivB, hindB,
    hsigsB, hslotsB, hsrc⟩ := facts
  obtain ⟨σ, hσ, hσn, hσm⟩ := alpha
  have hP := srcProg_eq hσ
  -- the pre-renaming `wmul_u128` renamed is the source `wmul_u128`
  have hfs : f0.rename σ.fwd = fs := pre_fn hP hσn hf
  have hsig0 : f0.sig = fs.sig := by rw [← hfs, Clif.Function.rename_sig]
  -- the base premises of `helperBase`
  have hind : ∀ g ∈ (prog J).funcs, Clif.IndFree g :=
    fun g hg => indFreeB_sound (List.all_eq_true.mp hindB g hg)
  have hdiv : ∀ g ∈ (prog J).funcs, ∀ e ∈ g.externs, (prog J).func? e.2.name = none →
      Clif.Rust.isDivHelper e.2.name = false := by
    intro g hg e he hn
    have := List.all_eq_true.mp (List.all_eq_true.mp hdivB g hg) e he
    simpa [hn] using this
  have hslots : ∀ g ∈ J.srcProg.funcs, g.slots = [] :=
    fun g hg => by simpa using List.all_eq_true.mp hslotsB g hg
  have hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f0.sig.params).getD []) args args' := by
    rw [hsig0, gp, Option.getD_some]
    exact ⟨⟨3#64, 1#64, rfl, rfl, rfl⟩, ⟨5#64, 0#64, rfl, rfl, rfl⟩, trivial⟩
  have hoc := outsideCall (memOf file) (BinCheck.roByte J S.data) hst
  have H := Front.bundle_correct_source (r := r (memOf file)) (args := args) (args' := args')
    (cs := cs.ren σ.symm) (cs' := cs') buildSpec_eq compile_eq hsrc hus hσ
    (helperEnv.ren σ.symm) helperBase (Front.Env.ren_symm_ren σ _).symm
    (Link.SourceWitness.baseOk_helper (fun g hg => by simpa using List.all_eq_true.mp htls g hg)
      hdiv hind (fun g hg => by simpa using List.all_eq_true.mp hsigsB g hg))
    (Link.DeadCleanup.SourceWitness.hooksSim_helper _)
    (fun _ => ⟨Link.SourceWitness.helperOk, Link.SourceWitness.extLegal,
      Link.SourceWitness.keepsBounded⟩)
    (fun ⟨g, hg, hn⟩ => absurd (hind g hg) hn) hf0 (by rw [hfs]; exact acyclic)
    (intact file) (by rw [hfs]; exact hoc) (by rw [hfs]; exact clifRun _)
    (pre_entry hfs clifEntry) hexp rfl (Front.Mem.ren_symm_ren σ cm).symm
    (pre_bnd hP (Link.SourceWitness.srcBounded hsrc hslots (Clif.Program.func?_some hf).1
      clifEntry cm_bounded)) M
  -- the pre-renaming run, from the linked one
  have hrun0 := pre_run hP run_eq
  have h := H.1 _ _ hrun0
  rw [hfs, hsig0, x30_r] at h
  obtain ⟨vals', hrel, k, hret, hx, -⟩ := h
  rw [gr, Option.getD_some] at hrel
  cases split_ret hrel
  exact ⟨buildSpec_eq, compile_eq, hus, sc_ok, hf0, f0_mentions, σ, hσ, hσm, hrun0, k, hret,
    hx 0 _ rfl, hx 1 _ rfl⟩

/-! ## The data closure of the whole unit -/

theorem unit_ok : (Front.parseUnit (unitWith fns)).toBool = true := by native_decide

/-- The whole unit, parsed. -/
def pu : Front.PCgu := getOk (Front.parseUnit (unitWith fns))

theorem pu_eq : Front.parseUnit (unitWith fns) = .ok pu := getOk_eq unit_ok

/-- The unit's parsed data objects. -/
abbrev ds : List Clif.DataObject := Front.okData (Front.dataParsed (unitWith fns).data)

/-- The data object `%name` of the unit's lines. -/
def obj (name : String) : Clif.DataObject := (ds.find? (·.name == name)).getD default

/-- The objects `c_Ldata3` (a relocation to `c_Ldata4`) and `c_Ldata4` (a string). -/
theorem data_facts :
    obj "c_Ldata3" ∈ ds ∧ obj "c_Ldata4" ∈ ds ∧ (obj "c_Ldata3").name = "c_Ldata3" ∧
    (obj "c_Ldata4").name = "c_Ldata4" ∧ "c_Ldata3" ∈ Front.rootsOf pu.funcs ∧
    "c_Ldata4" ∉ Front.rootsOf pu.funcs ∧ "c_Ldata4" ∈ (obj "c_Ldata3").refs := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- **Non-vacuity of the data closure** (`Front.data_complete`): the whole unit of `g_u128`
parses; `c_Ldata3`, which a function names, and `c_Ldata4`, which no function names but
`c_Ldata3` relocates to, are in its data closure. -/
theorem data_witness :
    Front.parseUnit (unitWith fns) = .ok pu ∧ obj "c_Ldata3" ∈ pu.data ∧
    obj "c_Ldata4" ∈ pu.data ∧ "c_Ldata4" ∉ Front.rootsOf pu.funcs := by
  obtain ⟨h3, h4, n3, n4, hr3, hn4, href⟩ := data_facts
  have r3 : Front.Reach ds (Front.rootsOf pu.funcs) (obj "c_Ldata3").name :=
    .root (by rw [n3]; exact hr3)
  have r4 : Front.Reach ds (Front.rootsOf pu.funcs) (obj "c_Ldata4").name :=
    .ref h3 r3 (by rw [n4]; exact href)
  exact ⟨pu_eq, Front.data_complete pu_eq h3 r3, Front.data_complete pu_eq h4 r4, hn4⟩

end Crates.FrontendBundleWitness
