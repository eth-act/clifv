import FV.E2E.LinkIdxSig
import FV.E2E.LinkWorldR

/-! # The class-aware link checks with the `blr` sites checked for their shape (#753, stage R4)

`linkChksTS`'s call-site check `siteOkC` asks a `blr` site to pass its arguments in the parameter
registers of every function of `P` it may enter (`blrOkC`, the premise `LinkSys.OkT.blrRegs`). That
is false of std's vtable calls next to calls of `sret` functions (#753). Under the register-guarded
world theorems (stages R2, R3, R3') a `blr` enters a function only with that function's registers
(`RegGuard`), so the link checks of `LinkSys.OkTR` ask of a `blr` site only its shape:

* `blrShapeB`: a `blr` site's target, uses and defs are vregs (an integer target), checked per site
  (`blrShapeB_sound`);
* `siteOkCRWith F g`, `siteOkCR P g`: `siteOkC` with `blrShapeB` at a `blr` site
  (`siteOkCR_sym_sound`, `siteOkCR_reg`);
* `retClsB`: every declared return of `g` and of its indirect-call signatures has its type's class
  (`retClass = tyClass`: no `sret`-purpose float return; `retClsB_sound`), which the register
  premise of the indirect calls (`RegCompatInd`) needs to turn `abiMatch` into equal return classes;
* `noCallSitesB`: the prepared code has no call site (`noCallSitesB_sound`, `NoCallSites`);
* `linkChksTSR`: `linkChksTS` with `siteOkCR` and `retClsB`; `linkChksWithTSXR`: its indexed form
  (`linkChksWithTSXR_of`).
-/

namespace E2E.LinkCheck
open Backend Backend.Proof

set_option autoImplicit false

/-- **A `blr` site's shape**: an integer target vreg, uses and defs on vregs. -/
def blrShapeB (info : CallInfo) : Bool :=
  match info.dest with
  | .reg (.vreg _ .int) =>
    (info.uses.all fun u => u.1.isVirtual = true) && (info.defs.all fun d => d.2.isVirtual = true)
  | _ => false

theorem blrShapeB_sound {info : CallInfo} (h : blrShapeB info = true) :
    ∃ t Lc Dc, info = ⟨.reg (.vreg t .int), argPairsC Lc, callDefsC Dc⟩ := by
  obtain ⟨d, us, ds⟩ := info
  unfold blrShapeB at h
  split at h
  · rename_i t hd
    simp only at hd
    subst hd
    simp only [Bool.and_eq_true] at h
    obtain ⟨hu, hdv⟩ := h
    exact ⟨t, us.map fun u => (regVN u.1, regVC u.1, u.2), ds.map fun d => (d.1, regVN d.2, regVC d.2),
      by rw [argPairsC_of_virtual hu, callDefsC_of_virtual hdv]⟩
  · cases h

/-- **The call sites of `g` with a `blr` site checked for its shape**: a `bl` of a function `h` of
`P` that `g` declares, uses and defs on vregs, arguments in `h`'s parameter registers and the
results from its return registers (`siteOkC`'s); a `bl` of an extern outside `P`; or a `blr` site
of the right shape (`blrShapeB`). `F`: the program's functions (`P.func?`, or a hash map). -/
def siteOkCRWith (F : String → Option Clif.Function) (g : Clif.Function) (info : CallInfo) : Bool :=
  match info.dest with
  | .sym n => match F n with
    | some h => g.externs.any (fun e => e.2.name == n) &&
        (info.uses.all fun u => u.1.isVirtual = true) &&
        (info.defs.all fun d => d.2.isVirtual = true) &&
        decide (info.uses.map (·.2) = regLocs h.sig) && defsOkC h.sig info.defs
    | none => true
  | .reg _ => blrShapeB info

/-- `siteOkCRWith` with the program's functions. -/
def siteOkCR (P : Clif.Program) (g : Clif.Function) (info : CallInfo) : Bool :=
  siteOkCRWith P.func? g info

/-- At a `bl` of a function of `P`: `siteOkC_sound`'s conclusion. -/
theorem siteOkCR_sym_sound {P : Clif.Program} {g : Clif.Function} {info : CallInfo}
    (h : siteOkCR P g info = true) {n : String} {h' : Clif.Function} (hd : info.dest = .sym n)
    (hf : P.func? n = some h') :
    (∃ e ∈ g.externs, e.2.name = n) ∧ ∃ Lc Dc,
      info = ⟨.sym n, argPairsC Lc, callDefsC Dc⟩ ∧ Lc.map (·.2.2) = regLocs h'.sig ∧
      (Dc.map (·.1)).take (sigRets h'.sig).length = (sigRetRegs h'.sig).take Dc.length := by
  obtain ⟨d, us, ds⟩ := info
  simp only at hd
  subst hd
  unfold siteOkCR siteOkCRWith at h
  simp only [hf, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hd, hu⟩, hdv⟩, h1⟩, h2⟩ := h
  refine ⟨hd, us.map fun u => (regVN u.1, regVC u.1, u.2), ds.map fun d => (d.1, regVN d.2, regVC d.2),
    by rw [argPairsC_of_virtual hu, callDefsC_of_virtual hdv], ?_, ?_⟩
  · simpa [List.map_map, Function.comp_def] using h1
  · simpa [defsOkC, List.map_map, Function.comp_def] using h2

/-- At a `blr` site: its shape. -/
theorem siteOkCR_reg {P : Clif.Program} {g : Clif.Function} {info : CallInfo}
    (h : siteOkCR P g info = true) (hreg : ∀ n, info.dest ≠ .sym n) :
    ∃ t Lc Dc, info = ⟨.reg (.vreg t .int), argPairsC Lc, callDefsC Dc⟩ := by
  obtain ⟨d, us, ds⟩ := info
  unfold siteOkCR siteOkCRWith at h
  cases d with
  | reg r => exact blrShapeB_sound h
  | sym n => exact absurd rfl (hreg n)

/-- **Every declared return of `g` and of its indirect-call signatures has its type's class**
(`retClass p = tyClass p.ty`: false only of an `sret`-purpose return of float type). -/
def retClsB (g : Clif.Function) : Bool :=
  g.sig.returns.all (fun p => decide (retClass p = tyClass p.ty)) &&
    (indSigs g).all fun s => s.returns.all fun p => decide (retClass p = tyClass p.ty)

theorem retClsB_sound {g : Clif.Function} (h : retClsB g = true) :
    (∀ p ∈ g.sig.returns, retClass p = tyClass p.ty) ∧
      ∀ s ∈ indSigs g, ∀ p ∈ s.returns, retClass p = tyClass p.ty := by
  simp only [retClsB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h

/-- **The prepared code has no call site** (no `call`, no `try_call`). -/
def noCallSitesB (vc : VCode) : Bool := allInsts vc (siteB fun _ => false)

theorem noCallSitesB_sound {vc : VCode} (h : noCallSitesB vc = true) : NoCallSites vc :=
  fun _ hs => Bool.false_ne_true (site_sound h hs)

/-- **`linkChksTS` with the `blr` sites checked for their shape** (`siteOkCR`) and the return
classes (`retClsB`). -/
def linkChksTSR (I : LinkInput) (P : Clif.Program) (T : List (Clif.Function × Art))
    (g : Clif.Function) (r : Except String Art) : List (String × Bool) :=
  let a := getOk r
  let fr := RAFrame.compute a.vcp a.rf
  [("outFits", g.externs.all (fun e => !(P.func? e.2.name).isSome || outFitsB e.2.sig fr.intBase)),
   ("calleeFrame/slotFits",
     !calleeB P (fun n => I.syms.lookup n) g || ((!g.slots.isEmpty || fr.size == a.af.frameSize - clobberBytes a.af.saves) && slotFitsB g a)),
   ("callRegs/blrShape", allInsts a.vcp (siteB (siteOkCR P g))),
   ("declSig", g.externs.all fun e => match P.func? e.2.name with
      | some h => decide (e.2.sig = h.sig)
      | none => true),
   ("raCall/raBlr", raCallB T g a),
   ("indScope/indSig", indBC P (fun n => I.syms.lookup n) g),
   ("retCls", retClsB g)]

/-- **`linkChksTSR` with the program's scans indexed** (`linkChksWithTSXR_of`): the entries of
`linkChksWithTSX` but the call-site check (`siteOkCRWith` with the program's functions `C.F`) and
`retClsB`. -/
def linkChksWithTSXR (C : LinkCtx) (X : LinkIdx)
    (SI : Std.HashMap (List Clif.Ty) (List Clif.Signature)) (g : Clif.Function)
    (r : Except String Art) : List (String × Bool) :=
  ((linkChksWithTSX C X SI g r).set 2
    ("callRegs/blrShape", allInsts (getOk r).vcp (siteB (siteOkCRWith C.F g)))) ++
    [("retCls", retClsB g)]

theorem linkChksWithTSXR_of (I : LinkInput) (P : Clif.Program) (T : List (Clif.Function × Art))
    (g : Clif.Function) (r : Except String Art) :
    linkChksWithTSXR (LinkCtx.of I P T) (LinkIdx.of P (LinkCtx.of I P T).ents)
      (sigIdx P (LinkCtx.of I P T).S) g r = linkChksTSR I P T g r := by
  have hF : (LinkCtx.of I P T).F = P.func? := by
    simp only [LinkCtx.of, funcMap_fun]
  simp only [linkChksWithTSXR, linkChksWithTSX_of, linkChksWithTS_of, hF]
  rfl

end E2E.LinkCheck
