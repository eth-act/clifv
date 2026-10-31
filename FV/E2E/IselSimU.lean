import FV.Backend.Proof.LowerSimU
import FV.E2E.Main
import FV.Backend.Proof.RefinesCSem
import FV.Backend.Proof.MemRefines

/-!
# CLIF → VCode with unwinding: `IselSimU` (S10e, #232)

`docs/plans/unwinding.md`, "The exceptional edge in the per-function theorem".

* `iselSimU_of_driver`: `IselSimU` from the driver simulation with unwinding
  (`driver_correctU`), for any activation semantics with the facts it uses (`RaiseSem`,
  `Refines`, `MemRefines`, `DriverSem`, and `DriverHyp` for the runs without raising callees);
  `csemU` (`iselSimU_csemU`, with `refines_csemU`, `memRefines_csemU`, `raiseSem_csemU`) and
  the dead-cleanup chain's `valueSemU` are instances;
* `callsRefine_csemU`/`indCallsRefine_csemU`: the callee contracts `DriverHyp` needs, for
  `csemU`, from the externs' contracts `XCallsOk`/`XCallsIndOk` and the exclusivity of normal
  returns and raises (`XRaiseExcl`);
* the validator's facts `UnwShape` come with the lowering obligations from `lowerCheckU`
  (`Driver.loweringU_of_check`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-! ## `csemU` -/

theorem refines_csemU (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (XR : XRaise) :
    Refines F (csemU F ctx X XR) := by
  intro i us w outs w' ctl h
  rw [csemU_of_not_call (fun info e => by subst e; simp [ispec] at h)
    (fun info ti e => by subst e; simp [ispec] at h)]
  exact refines_csem F ctx X i us w outs w' h

theorem memRefines_csemU (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (XR : XRaise)
    {sb : Nat} {syms : String → Option Nat} (hsb : ctx.slotBase = sb)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) :
    MemRefines F sb syms (csemU F ctx X XR) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := memRefines_csem F ctx X hsb hsym
  have e : ∀ i, (∀ info, i ≠ .call info) → (∀ info ti, i ≠ .tryCall info ti) →
      csemU F ctx X XR i = csem F ctx X i := fun _ hc ht => csemU_of_not_call hc ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro op d am fl uses w a h0 ha hav
    rw [e _ (fun _ h => by cases h) (fun _ _ h => by cases h)]; exact h1 op d am fl uses w a h0 ha hav
  · intro op d am fl v uses w a h0 ha hav
    rw [e _ (fun _ h => by cases h) (fun _ _ h => by cases h)]
    exact h2 op d am fl v uses w a h0 ha hav
  · intro d off w
    rw [e _ (fun _ h => by cases h) (fun _ _ h => by cases h)]; exact h3 d off w
  · intro d n b w hb
    rw [e _ (fun _ h => by cases h) (fun _ _ h => by cases h)]; exact h4 d n b w hb
  · intro ty d r fl u w hty hav
    rw [e _ (fun _ h => by cases h) (fun _ _ h => by cases h)]; exact h5 ty d r fl u w hty hav
  · intro ty d r fl u v w hty hav
    rw [e _ (fun _ h => by cases h) (fun _ _ h => by cases h)]; exact h6 ty d r fl u v w hty hav
  · intro ty op fl ra ro rd r1 r2 u x w hty hav
    rw [e _ (fun _ h => by cases h) (fun _ _ h => by cases h)]
    exact h7 ty op fl ra ro rd r1 r2 u x w hty hav
  · intro ty fl ra re rx rd r1 u e' x w hty hav
    rw [e _ (fun _ h => by cases h) (fun _ _ h => by cases h)]
    exact h8 ty fl ra re rx rd r1 u e' x w hty hav
  · intro d t n b w hb
    rw [e _ (fun _ h => by cases h) (fun _ _ h => by cases h)]; exact h9 d t n b w hb

theorem toEnv_extern {env : Clif.XEnv} {n : String} {g : List Clif.Val → Clif.Mem → Clif.Outcome}
    (h : env.toEnv.extern n = some g) :
    ∃ g0, env.extern n = some g0 ∧ ∀ v m, g v m = (g0 v m).toOutcome := by
  simp only [Clif.XEnv.toEnv, Option.map_eq_some_iff] at h
  obtain ⟨g0, h1, rfl⟩ := h
  exact ⟨g0, h1, fun _ _ => rfl⟩

theorem toOutcome_returned {o : Clif.XOutcome} {vals : List Clif.Val} {cm : Clif.Mem}
    (h : o.toOutcome = .returned vals cm) : o = .returned vals cm := by
  cases o with
  | returned v m =>
    simp only [Clif.XOutcome.toOutcome, Clif.Outcome.returned.injEq] at h
    rw [h.1, h.2]
  | _ => simp [Clif.XOutcome.toOutcome] at h

/-- **`CallsRefine` for `csemU`**, from the externs' contract and the exclusivity of normal
returns and raises (a callee that returns does not raise). -/
theorem callsRefine_csemU {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {XR : XRaise}
    {env : Clif.XEnv} {exts : List Clif.ExtFunc} {sigs : List Clif.Signature} {MR : MemRelT}
    (hX : XCallsOk env.toEnv exts MR X) (hE : XRaiseExcl env exts sigs MR X XR) :
    CallsRefine F env.toEnv exts MR (csemU F ctx X XR) := by
  refine ⟨fun n => X.sym n 0, fun rd n w => ⟨w, rfl, fun _ _ _ => rfl, fun _ _ => rfl, rfl⟩, ?_, ?_⟩
  · intro ext hin g sl cm w dest us ds uses args vals rvals cm' hg hd hds hargs hmr hret hrl
    obtain ⟨g0, hg0, hgg⟩ := toEnv_extern hg
    have hret0 := toOutcome_returned ((hgg vals cm).symm.trans hret)
    rcases hd with ⟨rfl, rfl⟩ | ⟨r, rfl, hcol, rfl⟩
    · have hnr := hE.1 ext hin g0 sl cm w (some ext.name) uses uses vals rvals cm' hg0
        (.inl ⟨rfl, rfl⟩) hargs hmr hret0
      obtain ⟨outs, w', hc, hol, ho, hm⟩ := hX ext hin g sl cm w (some ext.name) uses uses vals
        rvals cm' hg (.inl ⟨rfl, rfl⟩) hargs hmr hret hrl
      exact ⟨outs, w', by simp [csemU, callDest, hnr, csem, hc,
        List.take_of_length_le (show outs.length ≤ ds.length by omega)], by rw [hol, hds], ho, hm⟩
    · have hnr := hE.1 ext hin g0 sl cm w none _ args vals rvals cm' hg0
        (.inr ⟨rfl, hcol, rfl⟩) hargs hmr hret0
      obtain ⟨outs, w', hc, hol, ho, hm⟩ := hX ext hin g sl cm w none _ args vals rvals cm'
        hg (.inr ⟨rfl, hcol, rfl⟩) hargs hmr hret hrl
      exact ⟨outs, w', by simp [csemU, callDest, hnr, csem, hc,
        List.take_of_length_le (show outs.length ≤ ds.length by omega)], by rw [hol, hds], ho, hm⟩
  · intro ext hin g sl cm w dest us ds ti uses args vals rvals cm' hg hd hds hti hargs hmr hret hrl
    obtain ⟨g0, hg0, hgg⟩ := toEnv_extern hg
    have hret0 := toOutcome_returned ((hgg vals cm).symm.trans hret)
    rcases hd with ⟨rfl, rfl⟩ | ⟨r, rfl, hcol, rfl⟩
    · have hnr := hE.1 ext hin g0 sl cm w (some ext.name) uses uses vals rvals cm' hg0
        (.inl ⟨rfl, rfl⟩) hargs hmr hret0
      obtain ⟨outs, w', hc, hol, ho, hm⟩ := hX ext hin g sl cm w (some ext.name) uses uses vals
        rvals cm' hg (.inl ⟨rfl, rfl⟩) hargs hmr hret hrl
      refine ⟨_, w', by simp only [csemU, callDest, hnr, csem, hc, Option.filter_some, hol, hti,
        decide_true, ↓reduceIte, Option.map_some,
        List.take_of_length_le (show (outs ++ List.map (fun _ => ofX 0)
          (List.drop ext.sig.returns.length ds)).length ≤ ds.length by
            simp only [List.length_append, List.length_map, List.length_drop]; omega)]; rfl,
        ?_, ho.append _, hm⟩
      simp only [List.length_append, List.length_map, List.length_drop]
      omega
    · have hnr := hE.1 ext hin g0 sl cm w none _ args vals rvals cm' hg0
        (.inr ⟨rfl, hcol, rfl⟩) hargs hmr hret0
      obtain ⟨outs, w', hc, hol, ho, hm⟩ := hX ext hin g sl cm w none _ args vals rvals cm' hg
        (.inr ⟨rfl, hcol, rfl⟩) hargs hmr hret hrl
      refine ⟨_, w', by simp only [csemU, callDest, hnr, csem, hc, Option.filter_some, hol, hti,
        decide_true, ↓reduceIte, Option.map_some,
        List.take_of_length_le (show (outs ++ List.map (fun _ => ofX 0)
          (List.drop ext.sig.returns.length ds)).length ≤ ds.length by
            simp only [List.length_append, List.length_map, List.length_drop]; omega)]; rfl,
        ?_, ho.append _, hm⟩
      simp only [List.length_append, List.length_map, List.length_drop]
      omega

/-- **`IndCallsRefine` for `csemU`**, from the externs' indirect-call contract and the
exclusivity of normal returns and raises. -/
theorem indCallsRefine_csemU {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {XR : XRaise}
    {env : Clif.XEnv} {exts : List Clif.ExtFunc} {sigs : List Clif.Signature} {MR : MemRelT}
    {syms : String → Option Nat} (hX : XCallsIndOk env.toEnv sigs MR X)
    (hE : XRaiseExcl env exts sigs MR X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hMRs : ∀ sl cm w, MR sl cm w → cm.symbols = syms) :
    IndCallsRefine env.toEnv sigs MR (csemU F ctx X XR) := by
  refine ⟨?_, ?_⟩
  · intro sig hin n g sl cm w a r us ds u args vals rvals cm' hg hsg ha hu hds hlen hall hmr hret
      hrl hty
    have hs : X.sym n 0 = BitVec.ofNat 64 a := hsym n a (by rw [← hMRs sl cm w hmr]; exact ha)
    obtain ⟨g0, hg0, hgg⟩ := toEnv_extern hg
    have hret0 := toOutcome_returned ((hgg vals cm).symm.trans hret)
    have hnr := hE.2 sig hin n g0 sl cm w u args vals rvals cm' hg0 hsg (by rw [hu, hs]) hlen hall
      hmr hret0 hty
    obtain ⟨outs, w', hc, hol, ho, hm⟩ := hX sig hin n g sl cm w u args vals rvals cm' hg hsg
      (by rw [hu, hs]) hlen hall hmr hret hrl hty
    exact ⟨outs, w', by simp [csemU, callDest, hnr, csem, hc,
        List.take_of_length_le (show outs.length ≤ ds.length by omega)], by rw [hol, hds], ho, hm⟩
  · intro sig hin n g sl cm w a r us ds ti u args vals rvals cm' hg hsg ha hu hds hti hlen hall
      hmr hret hrl hty
    have hs : X.sym n 0 = BitVec.ofNat 64 a := hsym n a (by rw [← hMRs sl cm w hmr]; exact ha)
    obtain ⟨g0, hg0, hgg⟩ := toEnv_extern hg
    have hret0 := toOutcome_returned ((hgg vals cm).symm.trans hret)
    have hnr := hE.2 sig hin n g0 sl cm w u args vals rvals cm' hg0 hsg (by rw [hu, hs]) hlen hall
      hmr hret0 hty
    obtain ⟨outs, w', hc, hol, ho, hm⟩ := hX sig hin n g sl cm w u args vals rvals cm' hg hsg
      (by rw [hu, hs]) hlen hall hmr hret hrl hty
    refine ⟨_, w', by simp only [csemU, callDest, hnr, csem, hc, Option.filter_some, hol, hti,
      decide_true, ↓reduceIte, Option.map_some,
      List.take_of_length_le (show (outs ++ List.map (fun _ => ofX 0)
        (List.drop sig.returns.length ds)).length ≤ ds.length by
          simp only [List.length_append, List.length_map, List.length_drop]; omega)]; rfl,
      ?_, ho.append _, hm⟩
    simp only [List.length_append, List.length_map, List.length_drop]
    omega

/-! ## `IselSimU` -/

/-- **CLIF → VCode with unwinding** from the driver simulation (`driver_correctU`), for any
activation semantics `sem` with the facts the simulation uses: the driver's facts (`DriverSem`,
and `DriverHyp` — M4's contracts for the runs without raising callees, under `env.toEnv`),
`ispec` and the memory forms (`Refines`, `MemRefines`), the steps of raising calls
(`RaiseSem`), and the validator's exceptional-edge facts (`UnwShape`, from `lowerCheckU`). -/
theorem iselSimU_of_driver {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    {sem : Sem} {X : ExtSem} {XR : XRaise} {Γ : Rel} {env : Clif.XEnv} {p : Clif.Program}
    (H : DriverHyp f vc ctx st0 R gn bl A sem (fun sl cm w => Γ.holds f sl cm w) env.toEnv p)
    (HU : UnwShape f vc ctx R gn bl A) (hds : DriverSem sem) (hRef : Refines Γ.F sem)
    (hMem : MemRefines Γ.F Γ.slotOff Γ.syms sem) (hRS : RaiseSem Γ.F X XR sem)
    (hstk : CallsStack f Γ.out) (htstk : TryStack f Γ.out)
    (hXR : XRaiseOk env (f.externs.map (·.2)) (fun sl cm w => Γ.holds f sl cm w) X XR)
    (hXRi : XRaiseIndOk env (indSigs f) (fun sl cm w => Γ.holds f sl cm w) X XR)
    (hsym : ∀ n b, Γ.syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) :
    IselSimU sem XR Γ env p f vc := by
  have HR : RaiseHyp f sem (fun sl cm w => Γ.holds f sl cm w) env Γ.F X XR Γ.slotOff Γ.syms
      Γ.out :=
    ⟨hRS, hRef, hMem, mrStable_holds Γ f, outArgsOk_holds Γ f, memRelOk_holds Γ f, hstk, htstk,
      hXR, hXRi, hsym, fun sl cm w h => (memRelOk_holds Γ f).symbols sl cm w h⟩
  intro args cs w₀ ρ₀ hce hrel hargs htr fuel
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hrun := driver_correctU H HU HR hds hB0 hce.callers hce.func rfl hbody hterm hregs hty.symm
    hce.sig (ρ₀ := ρ₀) hrel hargs htr fuel
  refine ⟨fun vals cm h => ?_, fun c h => ?_, fun e cm h => ?_⟩
  · rw [h] at hrun
    obtain ⟨us, outs, w, cm0, hret, h1, h2, h3, h4, h5⟩ := hrun
    exact ⟨us, outs, w, hret, h1, h2, h3, h5 ▸ memRel_leave (memRel_free h4.1 _)⟩
  · rw [h] at hrun
    exact hrun
  · rw [h] at hrun
    obtain ⟨obj, w, cm0, hu, hex, h4, h5⟩ := hrun
    exact ⟨obj, w, hu, hex, h5 ▸ memRel_leave (memRel_free h4.1 _)⟩

/-- **`IselSimU` for `csemU`** (`iselSimU_of_driver` with `csemU`'s facts). -/
theorem iselSimU_csemU {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    {fctx : FnCtx} {X : ExtSem} {XR : XRaise} {Γ : Rel} {env : Clif.XEnv} {p : Clif.Program}
    (H : DriverHyp f vc ctx st0 R gn bl A (csemU Γ.F fctx X XR)
      (fun sl cm w => Γ.holds f sl cm w) env.toEnv p)
    (HU : UnwShape f vc ctx R gn bl A) (hslot : fctx.slotBase = Γ.slotOff)
    (hstk : CallsStack f Γ.out) (htstk : TryStack f Γ.out)
    (hXR : XRaiseOk env (f.externs.map (·.2)) (fun sl cm w => Γ.holds f sl cm w) X XR)
    (hXRi : XRaiseIndOk env (indSigs f) (fun sl cm w => Γ.holds f sl cm w) X XR)
    (hsym : ∀ n b, Γ.syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) :
    IselSimU (csemU Γ.F fctx X XR) XR Γ env p f vc :=
  iselSimU_of_driver H HU (driverSem_csemU Γ.F fctx X XR) (refines_csemU Γ.F fctx X XR)
    (memRefines_csemU Γ.F fctx X XR hslot hsym) (raiseSem_csemU Γ.F fctx X XR) hstk htstk hXR
    hXRi hsym

/-! ## Non-vacuity of the raising premises

The premises on the callees' exceptional results hold, for every memory relation, in an
environment whose externs all unwind (a Rust panic with object 77, which `tag 0`/`tag 1`
handlers catch), with the raising callees `XR`: `XRaiseOk`, `XRaiseIndOk`, `XRaiseExcl` and
`RaiseSem` of `csemU` — the exceptional premises of `iselSimU_of_driver`/`iselSimU_csemU` are
satisfiable by callees that do raise. (The lowering validator `lowerCheckU` accepts every
`try_call`/`try_call_indirect` function of `corpus/clif-regress/try_call.clif` and
`call_indirect.clif`.) -/

namespace IselSimUWitness

/-- A Rust panic with object `obj`. -/
def exn (obj : BitVec 64) : Clif.Exn := ⟨fun t => t == 0 || t == 1, [⟨.i64, obj⟩, ⟨.i64, 0⟩]⟩

/-- Every extern unwinds with object 77, keeping the memory. -/
def env : Clif.XEnv := { extern := fun _ => some fun _ m => .unwound (exn 77) m }

/-- Every callee raises object 77 and the unwinder restores the world unchanged. -/
def XR : XRaise := ⟨fun _ _ w => some (77, w)⟩

theorem exnRel : ExnRel (exn 77) 77 := ⟨rfl, rfl, rfl⟩

theorem xRaiseOk (exts : List Clif.ExtFunc) (MR : MemRelT) (X : ExtSem) :
    XRaiseOk env exts MR X XR := by
  intro ext _ g sl cm w d uses args vals e m hg _ _ hmr hu
  simp only [env, Option.some.injEq] at hg
  subst hg
  simp only [Clif.XOutcome.unwound.injEq] at hu
  obtain ⟨rfl, rfl⟩ := hu
  exact ⟨77, w, rfl, exnRel, hmr⟩

theorem xRaiseIndOk (sigs : List Clif.Signature) (MR : MemRelT) (X : ExtSem) :
    XRaiseIndOk env sigs MR X XR := by
  intro sig _ n g sl cm w u args vals e m hg _ _ _ _ hmr hu _
  simp only [env, Option.some.injEq] at hg
  subst hg
  simp only [Clif.XOutcome.unwound.injEq] at hu
  obtain ⟨rfl, rfl⟩ := hu
  exact ⟨77, w, rfl, exnRel, hmr⟩

theorem xRaiseExcl (exts : List Clif.ExtFunc) (sigs : List Clif.Signature) (MR : MemRelT)
    (X : ExtSem) : XRaiseExcl env exts sigs MR X XR := by
  refine ⟨fun ext _ g sl cm w d uses args vals rvals cm' hg _ _ _ hr => ?_,
    fun sig _ n g sl cm w u args vals rvals cm' hg _ _ _ _ _ hr _ => ?_⟩ <;>
  · simp only [env, Option.some.injEq] at hg
    subst hg
    cases hr

/-- `csemU` with these callees: a raising `call` ends the activation, a supported `tryCall`
continues at its first handler with the payload. -/
theorem raiseSem (F : BitVec 64 → Prop) (fctx : FnCtx) (X : ExtSem) :
    RaiseSem F X XR (csemU F fctx X XR) := raiseSem_csemU F fctx X XR

end IselSimUWitness

end E2E
