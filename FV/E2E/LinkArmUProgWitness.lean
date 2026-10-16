import FV.E2E.LinkArmUProg
import FV.E2E.LinkCheck
import FV.E2E.DeadCleanupUnwindWitness

/-!
# Non-vacuity of the whole-program theorem with unwinding (S10f, #233)

A concrete linked program with unwinding for which every premise of
`E2E.backend_correct_program_budgetU`/`_peakU` but the entry state's holds: `P = {f, h}` (parsed
from `srcF`, `srcH`, compiled by the compiler's pipeline with its spill fallback, `fallback`,
loaded at `0x10000`, `0x20000`), where `f` calls the program function `h` and `h` calls the base
extern `throw`, which raises: its CLIF semantics unwinds with the exception object `77`
(`throwEnvX`), its exceptional result at the Arm level is `77` with the world unchanged
(`IselSimUWitness.XR`), and on the machine it raises `77`, the unwinder restoring the call state
(`DeadCleanupUnwindWitness.Uw`). So the exception propagates through the program callee `h`
into `f`: the whole-program CLIF run from `f` on `41` ends `unwound` (`run_unwinds`), and the
linked machine with unwinding raises at `f`'s call of `h` (`praiseU`).

* `L_ok`: `LinkSys.Ok` (the checker `okB`, `LinkCheck.okB_sound`, with the base premises
  `baseOk`), `LU_okU`: `LinkSysU.OkU` (the per-function checks `uChk` decided by
  `native_decide`, the raising base callee's contracts), `noNI`: no non-interference is needed.
* `budgetU_applies`, `peakU_applies`: the theorems specialised to this system (left open: the
  entry state's premises, as in `DeadCleanupUnwindWitness.final_applies`).
-/

namespace E2E.LinkArmUProgWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.UnwindTables E2E.LinkCheck

def srcH : String := "function %h(i64) -> i64 system_v {
    fn0 = colocated %throw(i64) system_v
block0(v0: i64):
    call fn0(v0)
    return v0
}
"

def srcF : String := "function %f(i64) -> i64 system_v {
    fn0 = colocated %h(i64) -> i64 system_v
block0(v0: i64):
    v1 = call fn0(v0)
    return v1
}
"

def fiF : FnInput := { clif := srcF, ra := "{}" }
def fiH : FnInput := { clif := srcH, ra := "{}" }
def fF : Clif.Function := fiF.func
def fH : Clif.Function := fiH.func

/-- The input: `f`, `h`, the base extern `throw`, compiled by the compiler's pipeline. -/
def I : LinkInput where
  funcs := [fiF, fiH]
  addrs := [("f", 0x10000), ("h", 0x20000), ("throw", 0x30000)]
  syms := []
  raStar := 0x40000
  D := 4096
  fallback := true

/-- **The base environment with unwinding**: `throw` unwinds with the exception object `77`,
keeping the memory; nothing else outside the program has a semantics. -/
def throwEnvX : Clif.XEnv where
  extern n := if n = "throw" then some fun _ m => .unwound (IselSimUWitness.exn 77) m else none

/-- The base environment: `throwEnvX` read without unwinding, no machine-level normal result for
a call outside the program (`throw` never returns), calls outside the program continue at the
next instruction, no TLS. -/
def B : BaseEnv where
  env := throwEnvX.toEnv
  call _ _ _ := none
  tp := 0
  tlsFlags _ s := Arm.read_pstate s
  hooks := closedBase.hooks

/-- The linked system. -/
def L0 (F : BitVec 64 → Prop) : LinkSys := LinkSys.ofInput I B F

/-- **The linked system with unwinding**: the base callees raise `77` on the machine and at the
Arm level. -/
def LU (F : BitVec 64 → Prop) : LinkSysU :=
  { L0 F with Ub := DeadCleanupUnwindWitness.Uw, envX := throwEnvX, XRb := IselSimUWitness.XR }

theorem okB_true : okB I = true := by native_decide

theorem funcs_eq (F : BitVec 64 → Prop) : (LU F).P.funcs = [fF, fH] := rfl

/-- The per-function facts: no TLS, no indirect call, the unwinding validator and the tables,
no outgoing-argument area and no slot region. -/
def uChk : Bool :=
  [fF, fH].all fun g =>
    let a := artOf I.results g
    !hasTls g && indFreeB g && lowerCheckU g a.vc && (callSites a.af a.fa).toBool &&
      (unwindRows a.af a.fa).toBool && padsNonzeroB a.af a.fa && lastCallsOk a.af a.fa &&
      savedCheck a.vcp a.rf && (RAFrame.compute a.vcp a.rf).intBase == 0 &&
      (RAFrame.compute a.vcp a.rf).size == a.af.frameSize

theorem uChk_true : uChk = true := by native_decide

structure UFacts (g : Clif.Function) (a : Art) : Prop where
  tls : hasTls g = false
  indFree : Clif.IndFree g
  lowerU : lowerCheckU g a.vc = true
  sites : ∃ lsda, callSites a.af a.fa = .ok lsda
  rows : ∃ rows, unwindRows a.af a.fa = .ok rows
  pads : padsNonzeroB a.af a.fa = true
  last : lastCallsOk a.af a.fa = true
  saved : savedCheck a.vcp a.rf = true
  ib : (RAFrame.compute a.vcp a.rf).intBase = 0
  sz : (RAFrame.compute a.vcp a.rf).size = a.af.frameSize

theorem ok_of_toBool {ε α : Type} {x : Except ε α} (h : x.toBool = true) : ∃ a, x = .ok a := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl⟩

theorem ufacts {F : BitVec 64 → Prop} {g : Clif.Function} (hg : g ∈ (LU F).P.funcs) :
    UFacts g ((LU F).A g) := by
  rw [funcs_eq] at hg
  have h := uChk_true
  simp only [uChk, List.all_eq_true] at h
  have hc := h g hg
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hc
  exact ⟨h1, indFreeB_sound h2, h3, ok_of_toBool h4, ok_of_toBool h5, h6, h7, h8, h9, h10⟩

theorem throw_extern {n : String} {g : List Clif.Val → Clif.Mem → Clif.XOutcome}
    (h : throwEnvX.extern n = some g) :
    n = "throw" ∧ g = fun _ m => .unwound (IselSimUWitness.exn 77) m := by
  simp only [throwEnvX] at h
  split at h
  · exact ⟨by assumption, (Option.some.inj h).symm⟩
  · cases h

/-- The base externs never return normally (`throw` unwinds). -/
theorem base_noReturn {F : BitVec 64 → Prop} {n : String} {g : List Clif.Val → Clif.Mem → Clif.Outcome}
    (h : (L0 F).base.extern n = some g) {vals : List Clif.Val} {m m' : Clif.Mem}
    {rvals : List Clif.Val} : g vals m ≠ .returned rvals m' := by
  simp only [L0, LinkSys.ofInput, ofRes, B, Clif.XEnv.toEnv, Option.map_eq_some_iff] at h
  obtain ⟨g0, hg0, rfl⟩ := h
  obtain ⟨-, rfl⟩ := throw_extern hg0
  simp [Clif.XOutcome.toOutcome]

theorem allIndFree {F : BitVec 64 → Prop} : ¬ ∃ g ∈ (L0 F).P.funcs, ¬ Clif.IndFree g :=
  fun ⟨g, hg, hn⟩ => hn (ufacts (F := F) hg).indFree

/-- **The base premises hold** (`throw` never returns normally, nothing outside the program
returns at the Arm level, no TLS, no indirect call). -/
theorem baseOk (F : BitVec 64 → Prop) : BaseOk (L0 F) where
  baseNoAlloc := fun _ n g hn vals m rvals m' hr => absurd hr (base_noReturn hn)
  keepSyms := fun h => absurd h allIndFree
  aliasSyms := fun h => absurd h allIndFree
  baseOs := fun g hg info hs hb F' K G s0 Pc ctx s _ _ _ c wh ops regs i' w outs w' _ _ _ _ _ _
      _ hsem => by simp [csem, L0, LinkSys.ofInput, ofRes, B] at hsem
  basePc := fun d s _ _ _ => by
    simp [L0, LinkSys.ofInput, ofRes, B, closedBase, Arm.r_of_w_same]
  baseExt := fun d uses w outs w' _ hx => by simp [L0, LinkSys.ofInput, ofRes, B] at hx
  baseX := fun g hg F' slotOff out c => by
    intro ext _ gs sl cm w d uses args vals rvals cm' he _ _ _ hr
    exact absurd hr (base_noReturn he)
  baseXI := fun g hg F' slotOff out c sig hsig => by
    rw [indSigs_nil_of_indFree (ufacts (F := F) hg).indFree] at hsig; cases hsig
  baseTls := fun g hg ht => absurd ht (by simp [(ufacts (F := F) hg).tls])
  baseTry := fun g hg F' ctx info ti _ c wh ops regs i' s w outs w' s' _ _ _ _ _ _ hsem => by
    simp [csem, L0, LinkSys.ofInput, ofRes, B] at hsem
  baseNI := fun _ g hg F' c n sig vals cm args d uses Z w w' o x o' x' _ _ _ _ _ _ _ _ _ hx _ => by
    simp [L0, LinkSys.ofInput, ofRes, B] at hx
  baseTlsNI := fun _ F' => by
    intro Z n w w' _ hsw
    have e : ∀ fl, Arm.r (.FLAG fl) w = Arm.r (.FLAG fl) w' := fun fl => hsw.1 _ (by simp [Masked])
    have h1 := e .N
    have h2 := e .Z
    have h3 := e .C
    have h4 := e .V
    simp only [Arm.r, Arm.read_base_flag] at h1 h2 h3 h4
    show Arm.read_pstate w = Arm.read_pstate w'
    apply Arm.PState.ext <;> simp only [Arm.read_pstate] <;> assumption
  baseKeepsPlace := fun _ n g hn vals m rvals m' hr => absurd hr (base_noReturn hn)
  baseKeepsAllocs := fun _ n g hn vals m rvals m' hr => absurd hr (base_noReturn hn)

/-- **`LinkSys.Ok` holds** for every `F` containing the code. -/
theorem L_ok (F : BitVec 64 → Prop) (hF : ∀ a, (L0 F).Img a → F a) : (LU F).Ok :=
  okB_sound okB_true (baseOk F) hF

/-- **`LinkSysU.OkU` holds**: the per-function unwinding checks, and the raising base callee's
contracts (`throw` raises `77` at the Arm level and on the machine, the world and the call state
unchanged). -/
theorem LU_okU (F : BitVec 64 → Prop) : (LU F).OkU where
  envX := rfl
  lowerU g hg := (ufacts hg).lowerU
  sites g hg := (ufacts hg).sites
  rows g hg := (ufacts hg).rows
  pads g hg := (ufacts hg).pads
  last g hg := (ufacts hg).last
  saved g hg := (ufacts hg).saved
  indScopeX g hg hn := absurd (ufacts hg).indFree hn
  baseXR g hg F' slotOff out c := by
    intro ext _ G sl cm w d uses args vals e m hG _ _ hmr hu
    obtain ⟨-, rfl⟩ := throw_extern hG
    simp only [Clif.XOutcome.unwound.injEq] at hu
    obtain ⟨rfl, rfl⟩ := hu
    exact ⟨77, w, rfl, IselSimUWitness.exnRel, hmr⟩
  baseXRI g hg F' slotOff out c sig hsig := by
    rw [indSigs_nil_of_indFree (ufacts hg).indFree] at hsig; cases hsig
  baseExcl _ _ _ _ h := absurd rfl h
  baseRaiseExt d uses w obj w' _ h herr := by
    simp only [LU, IselSimUWitness.XR, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨herr, rfl⟩
  baseUnw g hg info hs hb i hi F' K G s0 Pc := by
    intro s _ _ _ c wh ops regs i' w _ _ _ _ hsw _ herr _ obj w' h
    simp only [LU, IselSimUWitness.XR, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨s, rfl, hsw, ⟨rfl, fun _ _ => rfl⟩, herr, rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  baseNoRaise g hg info hs hb i hi F' K G s0 Pc s _ _ _ c wh ops regs i' w _ _ _ _ _ _ _ _ h :=
    absurd rfl h
  baseKeepsPlaceU _ n G hG vals m e m' hu := by
    obtain ⟨-, rfl⟩ := throw_extern hG
    simp only [Clif.XOutcome.unwound.injEq] at hu
    rw [← hu.2]
  baseKeepsAllocsU _ n G hG vals m := by
    obtain ⟨-, rfl⟩ := throw_extern hG
    refine ⟨fun _ _ h => (by simp at h), fun e m' hu x hx => ?_⟩
    simp only [Clif.XOutcome.unwound.injEq] at hu
    rw [← hu.2] at hx
    exact hx

/-- **No non-interference is needed**: no function of `P` has an outgoing-argument area or a slot
region. -/
theorem noNI (F : BitVec 64 → Prop) : ¬ (LU F).NeedNI := by
  rintro ⟨g, hg, h, hc, hne⟩
  have hh := (LU F).toLinkSys.callee_mem hc
  have hu := ufacts hh
  rcases hne with h1 | h1
  · exact h1 hu.ib
  · exact h1 hu.sz

/-! ## The raise through a program callee -/

def isUnw77 : Clif.XOutcome → Bool
  | .unwound e _ => e.payload == [⟨.i64, 77#64⟩, ⟨.i64, 0#64⟩] && e.catches 0 && e.catches 1
  | _ => false

/-- The whole-program run with unwinding from `f` on `41` (empty memory) unwinds with `77`. -/
def runB : Bool :=
  match Clif.initState (LU (fun _ => True)).P "f" [⟨.i64, 41#64⟩] {} with
  | .ok cs => isUnw77 (Clif.runLoopX throwEnvX (LU (fun _ => True)).P 10 cs.toX)
  | _ => false

theorem runB_true : runB = true := by native_decide

theorem isUnw77_sound {o : Clif.XOutcome} (h : isUnw77 o = true) :
    ∃ e m, o = .unwound e m ∧ ExnRel e 77 := by
  cases o with
  | unwound e m =>
    simp only [isUnw77, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨e, m, rfl, h.1.1, h.1.2, h.2⟩
  | _ => simp [isUnw77] at h

/-- **The whole-program run with unwinding from `f` on `41` unwinds** (the exception `throw`
raises in `h` propagates through `h` and `f`), with an exception related to the object `77`. -/
theorem run_unwinds : ∃ cs, Clif.initState (LU (fun _ => True)).P "f" [⟨.i64, 41#64⟩] {} = .ok cs ∧
    ∃ e m, Clif.runLoopX throwEnvX (LU (fun _ => True)).P 10 cs.toX = .unwound e m ∧
      ExnRel e 77 := by
  have h := runB_true
  unfold runB at h
  split at h
  · rename_i cs hcs
    exact ⟨cs, hcs, isUnw77_sound h⟩
  · cases h

/-! ## The theorems apply -/

/-- **`backend_correct_program_budgetU` applies**: for every `F` containing the code, the linked
system with unwinding satisfies `Ok`, `OkU` (with a raising base callee: `throw` raises `77` at the
Arm level, on the machine and in CLIF), needs no non-interference, has the stack budget
`fun M _ => K M`; so for every entry state of `f` the linked machine with unwinding refines `f`'s
whole-program run with unwinding (which, from `f` on `41`, unwinds: `run_unwinds`). -/
theorem budgetU_applies (F : BitVec 64 → Prop) (hF : ∀ a, (L0 F).Img a → F a) :
    (LU F).Ok ∧ (LU F).OkU ∧ ¬ (LU F).NeedNI ∧ (LU F).Budget (fun M _ => (LU F).K M) ∧
    fF ∈ (LU F).P.funcs ∧ fH ∈ (LU F).P.funcs ∧
    (∀ uses w, (LU F).XRb.raise (some "throw") uses w = some (77, w)) ∧
    (∀ s, (LU F).Ub.raise (some "throw") s = some (77, s)) ∧
    (LU F).envX.extern "throw" = some (fun _ m => .unwound (IselSimUWitness.exn 77) m) ∧
    ∀ (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State},
      AbiEntry ((LU F).A fF).fb ((LU F).A fF).base ra s →
      StackAvail ((LU F).K M) ((LU F).A fF).af s →
      (LU F).F = frameWG ((LU F).K M) (RAFrame.compute ((LU F).A fF).vcp ((LU F).A fF).rf).intBase
        (RAFrame.compute ((LU F).A fF).vcp ((LU F).A fF).rf).size ((LU F).A fF).af (LU F).Img s →
      (∀ a, (LU F).Img a → ¬ StackBelow (frameDrop ((LU F).A fF).af + (LU F).K M) (spv s) a) →
      (∀ a, (LU F).Img a → s.mem a = (LU F).imgMem a) →
      BodyEntry ((LU F).A fF).af s w₀ → ArgsIn fF.sig args s → ClifEntry fF args cs →
      StackArgsAvoid (LU F).Img fF.sig args s →
      Rel.holds ⟨(LU F).F, (LU F).syms, ((LU F).A fF).af.slotBase,
        (RAFrame.compute ((LU F).A fF).vcp ((LU F).A fF).rf).intBase⟩ fF cs.frame.slots cs.mem w₀ →
      ((LU F).NeedSlots → (LU F).PlaceAt cs.mem (spv w₀)) →
      TrapsExplicitX ((LU F).stdX.envRX M fF) (LU F).P.bare cs →
      ArmRefinesU ((LU F).A fF).fb ((LU F).A fF).base ra ((LU F).machU M fF) s
        (Clif.runLoopX (LU F).envX (LU F).P (M + 1) cs.toX) := by
  have hL := L_ok F hF
  have hU := LU_okU F
  have hκ : (LU F).Budget (fun M _ => (LU F).K M) := (LU F).toLinkSys.budget_K hL
  have hfF : fF ∈ (LU F).P.funcs := by rw [funcs_eq]; simp
  refine ⟨hL, hU, noNI F, hκ, hfF, by rw [funcs_eq]; simp, fun _ _ => rfl, fun _ => rfl,
    rfl, fun M ra s w₀ args cs hent hres hFe hgfree himg hbe hargs hcs hsav hrel hpl
    htr => ?_⟩
  exact backend_correct_program_budgetU (LU F) hL hU hκ (noNI F) hfF M hent hres hFe hgfree himg hbe
    hargs hcs hsav hrel hpl htr

/-- **`backend_correct_program_peakU` applies** to the same system (the peak call depth `d` of
the whole-program run with unwinding, its fuel `Fu`). -/
theorem peakU_applies (F : BitVec 64 → Prop) (hF : ∀ a, (L0 F).Img a → F a) (Fu d : Nat)
    {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry ((LU F).A fF).fb ((LU F).A fF).base ra s)
    (hres : StackAvail ((LU F).K d) ((LU F).A fF).af s)
    (hFe : (LU F).F = frameWG ((LU F).K d)
      (RAFrame.compute ((LU F).A fF).vcp ((LU F).A fF).rf).intBase
      (RAFrame.compute ((LU F).A fF).vcp ((LU F).A fF).rf).size ((LU F).A fF).af (LU F).Img s)
    (hgfree : ∀ a, (LU F).Img a → ¬ StackBelow (frameDrop ((LU F).A fF).af + (LU F).K d) (spv s) a)
    (himg : ∀ a, (LU F).Img a → s.mem a = (LU F).imgMem a)
    (hbe : BodyEntry ((LU F).A fF).af s w₀) (hargs : ArgsIn fF.sig args s)
    (hcs : ClifEntry fF args cs) (hsav : StackArgsAvoid (LU F).Img fF.sig args s)
    (hrel : Rel.holds ⟨(LU F).F, (LU F).syms, ((LU F).A fF).af.slotBase,
      (RAFrame.compute ((LU F).A fF).vcp ((LU F).A fF).rf).intBase⟩ fF cs.frame.slots cs.mem w₀)
    (hpl : (LU F).NeedSlots → (LU F).PlaceAt cs.mem (spv w₀))
    (hd : Clif.DepthLeX (LU F).envX (LU F).P d cs.toX)
    (htr : TrapsExplicitX (((LU F).peakX Fu).envRX d fF) (LU F).P.bare cs) :
    ArmRefinesU ((LU F).A fF).fb ((LU F).A fF).base ra ((LU F).machU d fF) s
      (Clif.runLoopX (LU F).envX (LU F).P (Fu + 1) cs.toX) := by
  have hL := L_ok F hF
  exact backend_correct_program_peakU (LU F) hL (LU_okU F) ((LU F).toLinkSys.budget_K hL) (noNI F)
    (by rw [funcs_eq]; simp) Fu d hent hres hFe hgfree himg hbe hargs hcs hsav hrel hpl hd htr

end E2E.LinkArmUProgWitness
