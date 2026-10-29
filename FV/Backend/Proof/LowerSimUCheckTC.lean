module

public import FV.Backend.Proof.LowerSimUCheck
public import FV.Backend.Proof.DriverCheckTyC

@[expose] public section

/-!
# The exceptional-edge validator for typed `try_call`s (S11e6, #585)

`LowerSimUCheck.lean`'s `unwCheck` replays the integer lowering (`lowBlocks` with the integer
`try_call` helpers) and decides the exceptional-edge facts with `exnArgReg`: a handler-argument
value's register is `.vreg v .int`. A function with typed `try_call`s (`lowerCheckTC`'s
`lowBlocksC`/`tryRegsOfC`: float return vregs of the returns' classes) fails it. This file is
the class-aware copy:

* `exnArgRegC`: `exnArgReg` with the value's class from the context (`vregOf ctx`, the register
  the TC simulation's value renaming `LowerSimTC` uses); on an integer context it is
  `exnArgReg` (`exnArgRegC_int`);
* `TryExnTC`/`UnwShapeTC`: `TryExn`/`UnwShape` with `exnArgRegC` (everything else is
  class-independent: the payload registers `x0`/`x1` are integer, `payVreg`);
* `tryExnBTC`, `unwBlockBTC`, `unwOkTC`, `unwCheckTC`: the decided validator over
  `lowBlocksC` (exactly `lowerCheckTC`'s recording);
* `lowerCheckUTC f vc = lowerCheckTC f vc && unwCheckTC f vc`;
* soundness: `tryExnBTC_sound`, `unwShape_of_okTC`, `loweringUTC_of_check` — the TC analogue of
  `loweringU_of_check`: `LowerShapeTC`/`Cert`/`BrIdxTyped` (from `lowerCheckTC`) and
  `UnwShapeTC` for the same lowering record.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-! ## The class-aware facts -/

/-- `exnArgReg` with the handler-argument value's class from the context (`vregOf ctx`; the
class the TC lowering's value renaming uses, `LowerSimTC`). -/
def exnArgRegC (ctx : Ctx) (R : Reg → Reg) (ops : Array Operand) : Clif.TryArg → Reg
  | .val v => R (vregOf ctx v)
  | .exn i => match payVreg ops i with
    | some n => R (.vreg n .int)
    | none => .xzr
  | .ret _ => .xzr

/-- On an integer context the class-aware register of a handler argument is the integer one. -/
theorem exnArgRegC_int {ctx : Ctx} (hE : CtxE ctx) (R : Reg → Reg) (ops : Array Operand)
    (a : Clif.TryArg) : exnArgRegC ctx R ops a = exnArgReg R ops a := by
  cases a with
  | val v => simp only [exnArgRegC, exnArgReg, vregOf_int hE]
  | exn i => rfl
  | ret i => rfl

/-- `tryUOk` for the typed `try_call` shapes (`S11e6`, #585): the def operands are fixed to
`x0`/`x1` (the payload/integer-return registers) or to the float return registers `v0`..`v7`
(`tryRegsOfC` puts a `float` return's vreg in its ABI return register). -/
def tryUOkC (info : CallInfo) (ti : TryInfo) : Bool :=
  firstHandlerOk ti.handlers && !ti.clobberAll &&
    (defCons (.call info)).all (fun c => c == .fixed (.x 0) || c == .fixed (.x 1) ||
      match c with | .fixed (.v n) => decide (n ≤ 7) | _ => false) &&
    payloadRegOk info ti (.x 0) && payloadRegOk info ti (.x 1)

/-- `exnArgOk` with the typed-`try_call` exclusion: a handler-argument value must not be a
`float`-class def of the call — the exceptional edge defines only the `x0`/`x1` payload
registers (`payloadOuts`), so a `float` return's vreg is clobbered, not defined, on that edge
(in the integer lowering the return vregs are aliased to the payload vregs, `tryRegsOf`). -/
def exnArgOkC (ctx : Ctx) (ops : Array Operand) (a : Clif.TryArg) : Bool :=
  exnArgOk ops a &&
  match a with
  | .val v => !((ops.toList.filter Operand.isDef).any fun o =>
    o.cls = .float && o.vreg = (match vregOf ctx v with | .vreg n _ => n | _ => 0))
  | _ => true

/-- **The exceptional edge of a `try_call`/`try_call_indirect`** (`TryExn` with the class-aware
handler-argument registers). -/
def TryExnTC (f : Clif.Function) (vc : VCode) (ctx : Ctx) (R : Reg → Reg) (gn : Nat → Nat)
    (A : Nat → Nat → List Clif.ValueId) (bi : Nat) (B : Clif.Block) (L : BLow)
    (et : Clif.ExnTable) : Prop :=
  ∃ T n d rest pre c ops h eb tl, L.tl = some T ∧ et.items = .tag n d :: rest ∧ n ≤ 1 ∧
    L.tst'.emitted.toList = pre ++ [.call c] ∧ (∀ m ∈ pre, ∀ ci, m ≠ .call ci) ∧
    tryUOkC c T.info = true ∧ (MInst.call c).operands = .ok ops ∧
    (∀ o ∈ ops.toList.filter Operand.isDef, o.isLate = true) ∧
    ((ops.toList.filter Operand.isDef).map (·.vreg)).Nodup ∧
    T.info.handlers.head? = some h ∧ vc.blocks[h.label]? = some eb ∧ eb.insts = #[.jump tl] ∧
    eb.params = #[] ∧ eb.branchArgs = (d.args.map (exnArgRegC ctx R ops)).toArray ∧
    (∀ a ∈ d.args, exnArgOkC ctx ops a = true) ∧ blockIdx? f d.block = some tl ∧ tl ≠ 0 ∧
    ∀ TB, f.blocks[tl]? = some TB → EdgeCert ctx gn A bi B tl TB

/-- **The facts of the recorded lowering the exceptional runs use** (`UnwShape` with
`TryExnTC`). -/
structure UnwShapeTC (f : Clif.Function) (vc : VCode) (ctx : Ctx) (R : Reg → Reg) (gn : Nat → Nat)
    (bl : List BLow) (A : Nat → Nat → List Clif.ValueId) : Prop where
  /-- the code of a call statement contains a `call` -/
  calls : ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (j : Nat) (stm : Clif.Stmt) (sl : SLow),
    f.blocks[bi]? = some B → bl[bi]? = some L → B.body[j]? = some stm → L.sl[j]? = some sl →
    ((∃ fn args, stm.inst = .call fn args) ∨
      ∃ sig callee args, stm.inst = .callIndirect sig callee args) →
    ∃ ci, MInst.call ci ∈ sl.st'.emitted.toList
  /-- the exceptional edge of every `try_call` -/
  tries : ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (et : Clif.ExnTable), f.blocks[bi]? = some B →
    bl[bi]? = some L → IsTryWith B.term et → TryExnTC f vc ctx R gn A bi B L et

/-! ## The validator -/

/-- `TryExnTC`, decided (`tryExnB` with the class-aware handler-argument registers). -/
def tryExnBTC (f : Clif.Function) (vc : VCode) (ctx : Ctx) (gn : Nat → Nat) (bla : Array BLow)
    (In : Array (List Clif.ValueId)) (bi : Nat) (B : Clif.Block) (L : BLow) (et : Clif.ExnTable) :
    Bool :=
  match L.tl, et.items, L.tst'.emitted.toList.getLast? with
  | some T, .tag n d :: _, some (.call c) =>
    decide (n ≤ 1) && L.tst'.emitted.toList.dropLast.all notCallB && tryUOkC c T.info &&
    match (MInst.call c).operands, T.info.handlers.head?, blockIdx? f d.block with
    | .ok ops, some h, some tl =>
      defsLateB ops && d.args.all (exnArgOkC ctx ops) && decide (tl ≠ 0) &&
      edgeOk f ctx gn f.blocks.toArray bla In (Avail.of B L In bi) B.body.length d.block &&
      match vc.blocks[h.label]? with
      | some eb => decide (eb.insts = #[.jump tl]) && decide (eb.params = #[]) &&
          decide (eb.branchArgs = (d.args.map (exnArgRegC ctx (renOf gn) ops)).toArray)
      | none => false
    | _, _, _ => false
  | _, _, _ => false

/-- The per-block conditions of `UnwShapeTC`. -/
def unwBlockBTC (f : Clif.Function) (vc : VCode) (ctx : Ctx) (gn : Nat → Nat) (bla : Array BLow)
    (In : Array (List Clif.ValueId)) (bi : Nat) (B : Clif.Block) (L : BLow) : Bool :=
  (List.range B.body.length).all (fun j => match B.body[j]?, L.sl[j]? with
    | some stm, some sl => stmtCallB stm sl
    | _, _ => true) &&
  match B.term with
  | .tryCall _ _ et | .tryCallIndirect _ _ et => tryExnBTC f vc ctx gn bla In bi B L et
  | _ => true

/-- `UnwShapeTC` of the lowering record, decided. -/
def unwOkTC (f : Clif.Function) (vc : VCode) (ctx : Ctx) (gn : Nat → Nat) (bl : List BLow)
    (In : Array (List Clif.ValueId)) : Bool :=
  (List.range f.blocks.length).all fun bi => match f.blocks[bi]?, bl[bi]? with
    | some B, some L => unwBlockBTC f vc ctx gn bl.toArray In bi B L
    | _, _ => true

/-- **The exceptional-edge validator on the lowering `lowerCheckTC` records** (the
typed-try_call analogue of `unwCheck`). -/
def unwCheckTC (f : Clif.Function) (vc : VCode) : Bool :=
  match buildCtx f with
  | .error _ => false
  | .ok (ctx, _, st0) =>
    match lowBlocksC f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
        f.blocks.length with
    | none => false
    | some bl =>
      let gn := gnAt (gnTable st0.nextVreg (aliasOf f bl))
      unwOkTC f vc ctx gn bl (inFix f ctx gn)

/-- **The lowering validator with the exceptional edges, typed `try_call`s.** -/
def lowerCheckUTC (f : Clif.Function) (vc : VCode) : Bool := lowerCheckTC f vc && unwCheckTC f vc

theorem lowerCheckTC_of_U {f : Clif.Function} {vc : VCode} (h : lowerCheckUTC f vc = true) :
    lowerCheckTC f vc = true := by
  simp only [lowerCheckUTC, Bool.and_eq_true] at h
  exact h.1

/-! ## Soundness -/

theorem tryExnBTC_sound {f : Clif.Function} {vc : VCode} {ctx : Ctx} {gn : Nat → Nat}
    {bl : List BLow} {In : Array (List Clif.ValueId)} {bi : Nat} {B : Clif.Block} {L : BLow}
    {et : Clif.ExnTable}
    (hlen : bl.length = f.blocks.length)
    (hD : ∀ (tl : Nat) (TB : Clif.Block) (TL : BLow), f.blocks[tl]? = some TB → bl[tl]? = some TL →
      DefsAt ctx TB TL.start)
    (hB : f.blocks[bi]? = some B) (hL : bl[bi]? = some L)
    (h : tryExnBTC f vc ctx gn bl.toArray In bi B L et = true) :
    TryExnTC f vc ctx (renOf gn) gn (availOf f In) bi B L et := by
  unfold tryExnBTC at h
  split at h
  · rename_i T n d rest c hT hit hlast
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨hn, hpre⟩, hok⟩, h⟩ := h
    split at h
    · rename_i ops hh tl hops hhd htl
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
      obtain ⟨⟨⟨⟨hdl, hargs⟩, htl0⟩, hedge⟩, h⟩ := h
      split at h
      · rename_i eb heb
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨hi, hp⟩, hba⟩ := h
        simp only [defsLateB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hdl
        have hsplit := getLast?_split hlast
        have hDb := hD bi B L hB hL
        refine ⟨T, n, d, rest, _, c, ops, hh, eb, tl, hT, hit, hn, hsplit, ?_, hok, hops, hdl.1,
          hdl.2, hhd, heb, hi, hp, hba, hargs, htl, htl0, fun TB hTB => ?_⟩
        · intro m hm ci e
          subst e
          have := hpre _ hm
          simp [notCallB] at this
        · obtain ⟨h1, h2, h3⟩ := edgeOk_sound hlen hD hedge tl TB htl hTB
          refine ⟨h1, h2, fun x hx => ?_⟩
          rcases h3 x hx with h | ⟨h1, h2, h3⟩
          · exact .inl h
          · exact .inr ⟨h1, (mem_avail hB hDb).mpr h2, h3⟩
      · cases h
    · cases h
  · cases h

/-- **Soundness of `unwOkTC`**, for a lowering record whose blocks satisfy `DefsAt`. -/
theorem unwShape_of_okTC {f : Clif.Function} {vc : VCode} {ctx : Ctx} {gn : Nat → Nat}
    {bl : List BLow} {In : Array (List Clif.ValueId)} (hlen : bl.length = f.blocks.length)
    (hD : ∀ (tl : Nat) (TB : Clif.Block) (TL : BLow), f.blocks[tl]? = some TB → bl[tl]? = some TL →
      DefsAt ctx TB TL.start)
    (h : unwOkTC f vc ctx gn bl In = true) : UnwShapeTC f vc ctx (renOf gn) gn bl (availOf f In) := by
  have hblk : ∀ bi B L, f.blocks[bi]? = some B → bl[bi]? = some L →
      unwBlockBTC f vc ctx gn bl.toArray In bi B L = true := by
    intro bi B L hB hL
    have := all_range h (lt_of_getElem? hB)
    simpa [hB, hL] using this
  refine ⟨fun bi B L j stm sl hB hL hs hsl hc => ?_, fun bi B L et hB hL hT => ?_⟩
  · have h1 := hblk bi B L hB hL
    simp only [unwBlockBTC, Bool.and_eq_true] at h1
    have := all_range h1.1 (lt_of_getElem? hs)
    simp only [hs, hsl] at this
    unfold stmtCallB at this
    have hany : (sl.st'.emitted.toList.any fun m => !notCallB m) = true := by
      rcases hc with ⟨fn, args, he⟩ | ⟨sig, callee, args, he⟩ <;> rw [he] at this <;> exact this
    obtain ⟨m, hm, hmc⟩ := List.any_eq_true.mp hany
    cases m with
    | call ci => exact ⟨ci, hm⟩
    | _ => simp [notCallB] at hmc
  · have h1 := hblk bi B L hB hL
    simp only [unwBlockBTC, Bool.and_eq_true] at h1
    have h2 := h1.2
    have hte : tryExnBTC f vc ctx gn bl.toArray In bi B L et = true := by
      rcases hT with ⟨fn, args, he⟩ | ⟨c, args, he⟩ <;> rw [he] at h2 <;> exact h2
    exact tryExnBTC_sound hlen hD hB hL hte

/-- **Soundness of the typed-try_call lowering validator with the exceptional edges**: the
lowering obligations (`loweringTC_of_check`) and `UnwShapeTC`, for the same lowering record and
certificate. -/
theorem loweringUTC_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheckUTC f vc = true) :
    ∃ ctx st0 R gn bl A, LowerShapeTC f vc ctx st0 R gn bl ∧ Cert f ctx st0 gn bl A ∧
      (∀ B ∈ f.blocks, BrIdxTyped ctx B.term) ∧ UnwShapeTC f vc ctx R gn bl A := by
  simp only [lowerCheckUTC, Bool.and_eq_true] at h
  obtain ⟨hc, hu⟩ := h
  unfold unwCheckTC at hu
  split at hu
  · cases hu
  · rename_i ctx ranges st0 hb
    split at hu
    · cases hu
    · rename_i bl hl
      unfold lowerCheckTC at hc
      rw [hb] at hc
      dsimp only at hc
      rw [hl] at hc
      dsimp only at hc
      simp only [Bool.and_eq_true] at hc
      have hS := lowerShapeTC_of_ok (gn := gnAt (gnTable st0.nextVreg (aliasOf f bl))) hb hl
        (fun n hn => gnAt_temp hn) hc.1.1.1.1
      have hcert := hc.1.1.1.2
      have hD : ∀ (tl : Nat) (TB : Clif.Block) (TL : BLow), f.blocks[tl]? = some TB →
          bl[tl]? = some TL → DefsAt ctx TB TL.start := by
        intro tl TB TL hTB hTL
        simp only [certOk, Bool.and_eq_true] at hcert
        have := all_range hcert.1.1.2 (by simpa using lt_of_getElem? hTB)
        have hok : certBlockOk f ctx st0 (gnAt (gnTable st0.nextVreg (aliasOf f bl)))
            f.blocks.toArray bl.toArray (inFix f ctx (gnAt (gnTable st0.nextVreg (aliasOf f bl))))
            tl TB TL = true := by
          simpa [List.getElem?_toArray, hTB, hTL] using this
        exact (certBlockOk_spec hok).2.1
      exact ⟨ctx, st0, _, _, bl, _, hS, cert_of_ok hS.len hcert, brIdx_of_ok hc.1.1.2,
        unwShape_of_okTC hS.len hD hu⟩

end Backend.Proof.Driver
