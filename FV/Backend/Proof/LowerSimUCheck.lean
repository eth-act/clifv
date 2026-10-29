module

public import FV.Backend.Proof.DriverCheckSound
public import FV.E2E.UnwindSem
import FV.Backend.Proof.IselInterp
import FV.Arm.MinTheory

public section

/-!
# The lowering validator for the exceptional edges (S10e, #232)

`docs/plans/unwinding.md`, "The exceptional edge in the per-function theorem". The driver
simulation with unwinding (`LowerSimU.lean`) needs, beside `LowerShape`/`Cert` (`lowerCheck`),
facts about the recorded lowering that only the exceptional runs use:

* the code of every `call`/`call_indirect` statement contains a `call` (where a raising callee
  ends the activation, `stmt_raise`);
* for every `try_call`/`try_call_indirect` (`TryExn`): the `lower_branch` code ends in the
  `call` that becomes the `tryCall`, with no earlier `call`; the call's shape is supported
  (`tryUOk`), its def operands are late with distinct vregs; the first exception-table item is a
  `tag 0`/`tag 1` handler `d` (Rust's personality catches every panic there, `ExnRel`), the
  first handler of the `try_call_info` is its landing pad: an edge block holding `jump` to `d`'s
  block, whose branch arguments are `d`'s arguments (`exnN` = the call's def in `xN`,
  `exnArgReg`); and the edge into `d`'s block satisfies `Cert`'s edge conditions (`Cert.term`
  covers only the normal-return edge, `edgeIds`).

`lowerCheckU f vc = lowerCheck f vc && unwCheck f vc` decides them on the compiler's output;
`loweringU_of_check` is its soundness: the lowering obligations of `lowering_of_check` and
`UnwShape` for the same lowering record and certificate.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-! ## The facts -/

/-- The vreg of the first def operand of `ops` fixed to `x i` (the payload register `i`). -/
def payVreg (ops : Array Operand) (i : Nat) : Option Nat :=
  ((ops.toList.filter Operand.isDef).find? fun o => o.con == .fixed (.x i)).map (·.vreg)

/-- The register an exception edge passes for a handler argument: a value's (renamed) vreg, the
call's def in payload register `i` for `exnN`. -/
@[expose] def exnArgReg (R : Reg → Reg) (ops : Array Operand) : Clif.TryArg → Reg
  | .val v => R (.vreg v .int)
  | .exn i => match payVreg ops i with
    | some n => R (.vreg n .int)
    | none => .xzr
  | .ret _ => .xzr

/-- A handler argument the edge supports: a value, or one of the two payload words held by a def
of the call. -/
def exnArgOk (ops : Array Operand) : Clif.TryArg → Bool
  | .val _ => true
  | .exn i => decide (i < 2) && (payVreg ops i).isSome
  | .ret _ => false

/-- The def operands of `ops` are late, with distinct vregs. -/
@[expose] def defsLateB (ops : Array Operand) : Bool :=
  (ops.toList.filter Operand.isDef).all (·.isLate) &&
    decide ((ops.toList.filter Operand.isDef).map (·.vreg)).Nodup

/-- `m` is no `call`. -/
@[expose] def notCallB : MInst → Bool
  | .call _ => false
  | _ => true

/-- `Cert`'s edge conditions for the edge from block `bi` (`B`, at its terminator) into block
`tl` (`TB`). -/
def EdgeCert (ctx : Ctx) (gn : Nat → Nat) (A : Nat → Nat → List Clif.ValueId) (bi : Nat)
    (B : Clif.Block) (tl : Nat) (TB : Clif.Block) : Prop :=
  (TB.params.map (·.1)).Nodup ∧
  (∀ x ∈ A tl 0, x ∉ TB.params.map (·.1) → ∀ d info cl, ctx.defInst? x = some d →
    ctx.insts[d]? = some info → info.clif = some cl → ∀ y ∈ instArgs cl,
      y ∉ TB.params.map (·.1)) ∧
  ∀ x ∈ A tl 0, (x ∈ TB.params.map (·.1) ∧ ctx.defInst? x = none) ∨
    (x ∉ TB.params.map (·.1) ∧ x ∈ A bi B.body.length ∧ gn x ∉ TB.params.map (·.1))

/-- **The exceptional edge of a `try_call`/`try_call_indirect`** (exception table `et`) of block
`bi` (`B`, lowered as `L`). -/
def TryExn (f : Clif.Function) (vc : VCode) (ctx : Ctx) (R : Reg → Reg) (gn : Nat → Nat)
    (A : Nat → Nat → List Clif.ValueId) (bi : Nat) (B : Clif.Block) (L : BLow)
    (et : Clif.ExnTable) : Prop :=
  ∃ T n d rest pre c ops h eb tl, L.tl = some T ∧ et.items = .tag n d :: rest ∧ n ≤ 1 ∧
    L.tst'.emitted.toList = pre ++ [.call c] ∧ (∀ m ∈ pre, ∀ ci, m ≠ .call ci) ∧
    tryUOk c T.info = true ∧ (MInst.call c).operands = .ok ops ∧
    (∀ o ∈ ops.toList.filter Operand.isDef, o.isLate = true) ∧
    ((ops.toList.filter Operand.isDef).map (·.vreg)).Nodup ∧
    T.info.handlers.head? = some h ∧ vc.blocks[h.label]? = some eb ∧ eb.insts = #[.jump tl] ∧
    eb.params = #[] ∧ eb.branchArgs = (d.args.map (exnArgReg R ops)).toArray ∧
    (∀ a ∈ d.args, exnArgOk ops a = true) ∧ blockIdx? f d.block = some tl ∧ tl ≠ 0 ∧
    ∀ TB, f.blocks[tl]? = some TB → EdgeCert ctx gn A bi B tl TB

/-- **The facts of the recorded lowering the exceptional runs use.** -/
structure UnwShape (f : Clif.Function) (vc : VCode) (ctx : Ctx) (R : Reg → Reg) (gn : Nat → Nat)
    (bl : List BLow) (A : Nat → Nat → List Clif.ValueId) : Prop where
  /-- the code of a call statement contains a `call` -/
  calls : ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (j : Nat) (stm : Clif.Stmt) (sl : SLow),
    f.blocks[bi]? = some B → bl[bi]? = some L → B.body[j]? = some stm → L.sl[j]? = some sl →
    ((∃ fn args, stm.inst = .call fn args) ∨
      ∃ sig callee args, stm.inst = .callIndirect sig callee args) →
    ∃ ci, MInst.call ci ∈ sl.st'.emitted.toList
  /-- the exceptional edge of every `try_call` -/
  tries : ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (et : Clif.ExnTable), f.blocks[bi]? = some B →
    bl[bi]? = some L → IsTryWith B.term et → TryExn f vc ctx R gn A bi B L et

/-! ## The validator -/

/-- `UnwShape.calls` for one statement. -/
@[expose] def stmtCallB (stm : Clif.Stmt) (sl : SLow) : Bool :=
  match stm.inst with
  | .call .. | .callIndirect .. => sl.st'.emitted.toList.any fun m => !notCallB m
  | _ => true

/-- `TryExn`, decided (the edge conditions as `certBlockOk` checks them, `edgeOk`). -/
def tryExnB (f : Clif.Function) (vc : VCode) (ctx : Ctx) (gn : Nat → Nat) (bla : Array BLow)
    (In : Array (List Clif.ValueId)) (bi : Nat) (B : Clif.Block) (L : BLow) (et : Clif.ExnTable) :
    Bool :=
  match L.tl, et.items, L.tst'.emitted.toList.getLast? with
  | some T, .tag n d :: _, some (.call c) =>
    decide (n ≤ 1) && L.tst'.emitted.toList.dropLast.all notCallB && tryUOk c T.info &&
    match (MInst.call c).operands, T.info.handlers.head?, blockIdx? f d.block with
    | .ok ops, some h, some tl =>
      defsLateB ops && d.args.all (exnArgOk ops) && decide (tl ≠ 0) &&
      edgeOk f ctx gn f.blocks.toArray bla In (Avail.of B L In bi) B.body.length d.block &&
      match vc.blocks[h.label]? with
      | some eb => decide (eb.insts = #[.jump tl]) && decide (eb.params = #[]) &&
          decide (eb.branchArgs = (d.args.map (exnArgReg (renOf gn) ops)).toArray)
      | none => false
    | _, _, _ => false
  | _, _, _ => false

/-- The per-block conditions of `UnwShape`. -/
def unwBlockB (f : Clif.Function) (vc : VCode) (ctx : Ctx) (gn : Nat → Nat) (bla : Array BLow)
    (In : Array (List Clif.ValueId)) (bi : Nat) (B : Clif.Block) (L : BLow) : Bool :=
  (List.range B.body.length).all (fun j => match B.body[j]?, L.sl[j]? with
    | some stm, some sl => stmtCallB stm sl
    | _, _ => true) &&
  match B.term with
  | .tryCall _ _ et | .tryCallIndirect _ _ et => tryExnB f vc ctx gn bla In bi B L et
  | _ => true

/-- `UnwShape` of the lowering record, decided. -/
def unwOk (f : Clif.Function) (vc : VCode) (ctx : Ctx) (gn : Nat → Nat) (bl : List BLow)
    (In : Array (List Clif.ValueId)) : Bool :=
  (List.range f.blocks.length).all fun bi => match f.blocks[bi]?, bl[bi]? with
    | some B, some L => unwBlockB f vc ctx gn bl.toArray In bi B L
    | _, _ => true

/-- The exceptional-edge validator on the lowering `lowerCheck` records. -/
def unwCheck (f : Clif.Function) (vc : VCode) : Bool :=
  match buildCtx f with
  | .error _ => false
  | .ok (ctx, _, st0) =>
    match lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
        f.blocks.length with
    | none => false
    | some bl =>
      let gn := gnAt (gnTable st0.nextVreg (aliasOf f bl))
      unwOk f vc ctx gn bl (inFix f ctx gn)

/-- **The lowering validator with the exceptional edges.** -/
def lowerCheckU (f : Clif.Function) (vc : VCode) : Bool := lowerCheck f vc && unwCheck f vc

theorem lowerCheck_of_U {f : Clif.Function} {vc : VCode} (h : lowerCheckU f vc = true) :
    lowerCheck f vc = true := by
  simp only [lowerCheckU, Bool.and_eq_true] at h
  exact h.1

/-! ## Soundness -/

theorem getLast?_split {α : Type} {l : List α} {a : α} (h : l.getLast? = some a) :
    l = l.dropLast ++ [a] := by
  have hne : l ≠ [] := by rintro rfl; simp at h
  rw [List.getLast?_eq_some_getLast hne] at h
  cases h
  exact (List.dropLast_concat_getLast hne).symm

theorem tryExnB_sound {f : Clif.Function} {vc : VCode} {ctx : Ctx} {gn : Nat → Nat}
    {bl : List BLow} {In : Array (List Clif.ValueId)} {bi : Nat} {B : Clif.Block} {L : BLow}
    {et : Clif.ExnTable}
    (hlen : bl.length = f.blocks.length)
    (hD : ∀ (tl : Nat) (TB : Clif.Block) (TL : BLow), f.blocks[tl]? = some TB → bl[tl]? = some TL →
      DefsAt ctx TB TL.start)
    (hB : f.blocks[bi]? = some B) (hL : bl[bi]? = some L)
    (h : tryExnB f vc ctx gn bl.toArray In bi B L et = true) :
    TryExn f vc ctx (renOf gn) gn (availOf f In) bi B L et := by
  unfold tryExnB at h
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

/-- **Soundness of `unwOk`**, for a lowering record whose blocks satisfy `DefsAt` (`certOk`). -/
theorem unwShape_of_ok {f : Clif.Function} {vc : VCode} {ctx : Ctx} {gn : Nat → Nat}
    {bl : List BLow} {In : Array (List Clif.ValueId)} (hlen : bl.length = f.blocks.length)
    (hD : ∀ (tl : Nat) (TB : Clif.Block) (TL : BLow), f.blocks[tl]? = some TB → bl[tl]? = some TL →
      DefsAt ctx TB TL.start)
    (h : unwOk f vc ctx gn bl In = true) : UnwShape f vc ctx (renOf gn) gn bl (availOf f In) := by
  have hblk : ∀ bi B L, f.blocks[bi]? = some B → bl[bi]? = some L →
      unwBlockB f vc ctx gn bl.toArray In bi B L = true := by
    intro bi B L hB hL
    have := all_range h (lt_of_getElem? hB)
    simpa [hB, hL] using this
  refine ⟨fun bi B L j stm sl hB hL hs hsl hc => ?_, fun bi B L et hB hL hT => ?_⟩
  · have h1 := hblk bi B L hB hL
    simp only [unwBlockB, Bool.and_eq_true] at h1
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
    simp only [unwBlockB, Bool.and_eq_true] at h1
    have h2 := h1.2
    have hte : tryExnB f vc ctx gn bl.toArray In bi B L et = true := by
      rcases hT with ⟨fn, args, he⟩ | ⟨c, args, he⟩ <;> rw [he] at h2 <;> exact h2
    exact tryExnB_sound hlen hD hB hL hte

/-- **Soundness of the lowering validator with the exceptional edges**: the lowering
obligations (`lowering_of_check`) and `UnwShape`, for the same lowering record and certificate. -/
theorem loweringU_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheckU f vc = true) :
    ∃ ctx st0 R gn bl A, LowerShape f vc ctx st0 R gn bl ∧ Cert f ctx st0 gn bl A ∧
      (∀ B ∈ f.blocks, BrIdxTyped ctx B.term) ∧ UnwShape f vc ctx R gn bl A := by
  simp only [lowerCheckU, Bool.and_eq_true] at h
  obtain ⟨hc, hu⟩ := h
  unfold unwCheck at hu
  split at hu
  · cases hu
  · rename_i ctx ranges st0 hb
    split at hu
    · cases hu
    · rename_i bl hl
      unfold lowerCheck at hc
      rw [hb] at hc
      dsimp only at hc
      rw [hl] at hc
      dsimp only at hc
      simp only [Bool.and_eq_true] at hc
      have hS := lowerShape_of_ok (gn := gnAt (gnTable st0.nextVreg (aliasOf f bl))) hb hl
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
        unwShape_of_ok hS.len hD hu⟩

end Backend.Proof.Driver
