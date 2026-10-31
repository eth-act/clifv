import FV.Backend.Proof.SpillEdgesLowT
import FV.Backend.Proof.LowerCompleteT
import FV.Backend.Proof.LowerDecide
import FVTest.Backend.FloatDriverT

/-!
Non-vacuity of the typed terminator shapes and of the typed validator's completeness (S11e5
Stage C): on the float-movement function `fMv` (float `return`, `brif` on an `i8` with float edge
arguments, `jump` with a float argument), on `fTb` (`br_table` on an `i32`, returning an `f64`
and an `f32`) and on `fCall` (an integer `call` between float values),
`lowerShapeT_of_lowerT`/`shapeOkT_completeT` hold without a premise on the terminator rules,
`LowT.raw_back` gives the last instruction of each block, and `lowerCheckT_complete` makes
`lowerCheckT` accept the lowerings (which the integer `lowerCheck` rejects). A `brif` on a
float value is outside `Compile.functionET` (`TermIntPos`). Checks by `native_decide` (witness
only). `lake build FVTest.Backend.FloatTermT`.
-/

open Backend Backend.Proof Backend.Proof.Driver

namespace FloatTermT

open FloatDriverT

/-- A `br_table` on an integer index, returning floats of both widths. -/
def fTb : Clif.Function := fnOfText
  "function %tb(i32, f64, f32) -> f64, f32 {
block0(v0: i32, v1: f64, v2: f32):
    br_table v0, block1, [block2, block1]
block1:
    return v1, v2
block2:
    v3 = f64const 0x1.0p-2
    return v3, v2
}
"

-- `fTb` parses, is in the typed scope and not in E; a float `brif` condition is not in the scope
#guard fTb.blocks.length == 3
#guard Compile.functionET fTb && !Compile.functionE fTb
#guard !Compile.functionET (fnOfText
  "function %b(f64) -> f64 {\nblock0(v0: f64):\n    brif v0, block1, block1\nblock1:\n    return v0\n}\n")
#guard (lowerFunction fTb).toBool
-- `fTb`'s return pins the float registers
#guard (vcOf fTb).blocks.any fun vb => vb.insts.any fun
  | .rets rs => rs.any (·.2 == .v 0) && rs.any (·.2 == .v 1)
  | _ => false

theorem functionET_tb : Compile.functionET fTb = true := by native_decide

/-- `fTb` is in the typed lowering's input conditions. -/
theorem scopeT_tb : LowerScopeT fTb where
  subsetT := functionET_tb
  nonempty := by native_decide
  noEntryPred := by native_decide
  ctxFacts := by
    intro ctx ranges st0 hb
    have h : (match buildCtx fTb with
        | .ok (c, _, _) => brIdxOk fTb c && ctxOkT fTb c
        | .error _ => false) = true := by native_decide
    rw [hb] at h
    simp only [Bool.and_eq_true] at h
    exact ⟨h.1, (ctxOkT_sound h.2).addr64⟩
  tryRet := by
    have h : fTb.blocks.all (fun B => !B.term.isTry) = true := by native_decide
    intro B hB et ht
    have := List.all_eq_true.mp h B hB
    rcases ht with ⟨fn, args, he⟩ | ⟨c, args, he⟩ <;> rw [he] at this <;> cases this
  stackLayout := by
    have h : fTb.blocks.all (fun B => B.body.all fun st => !(st.inst matches .call ..) ) = true := by
      native_decide
    have h2 : fTb.blocks.all (fun B => !B.term.isTry) = true := by native_decide
    refine ⟨fun B hB st hst fn args e hi _ => ?_, fun B hB fn args et e ht _ => ?_⟩
    · have := List.all_eq_true.mp (List.all_eq_true.mp h B hB) st hst
      rw [hi] at this; cases this
    · have := List.all_eq_true.mp h2 B hB
      rw [ht] at this; cases this
  indStackLayout := by
    have h : (Backend.indSigs fTb).all (fun s => stackLayoutOk s) = true := by native_decide
    exact fun s hs => List.all_eq_true.mp h s hs

theorem lowerFunction_tb : lowerFunction fTb = .ok (vcOf fTb) := by
  have hok : (lowerFunction fTb).toBool = true := by native_decide
  unfold vcOf
  cases h : lowerFunction fTb with
  | error e => rw [h] at hok; cases hok
  | ok vc => rfl

/-- `buildCtx`'s context and the recorded lowering of `f` (empty if they fail). -/
def ctxBlOf (f : Clif.Function) : Ctx × List BLow :=
  match buildCtx f with
  | .ok (ctx, _, st0) =>
    (ctx, (lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
      f.blocks.length).getD [])
  | .error _ => ({ func := f, insts := #[], valTy := #[], valDef := #[], valReg := #[], slotOff := [] }, [])

theorem ctxBlOf_eq {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    {bl : List BLow} (hb : buildCtx f = .ok (ctx, ranges, st0))
    (hl : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0 f.blocks.length =
      some bl) : ctxBlOf f = (ctx, bl) := by
  simp [ctxBlOf, hb, hl]

/-- Aliases none of whose targets is aliased are well founded. -/
theorem aliasWF_of_flat {al : List (Nat × Nat)}
    (h : al.all (fun p => al.all fun q => q.1 != p.2) = true) : AliasWF al :=
  ⟨fun _ => 0, fun p hp q hq he => by
    have := List.all_eq_true.mp (List.all_eq_true.mp h p hp) q hq
    simp [he] at this⟩

-- the recorded aliases of `fMv` and `fTb` have unique keys and no chains
#guard ((aliasOf fMv (ctxBlOf fMv).2).map (·.1)).Nodup
#guard ((aliasOf fTb (ctxBlOf fTb).2).map (·.1)).Nodup

/-- **Witness**: `lowerShapeT_of_lowerT` on a float function (`return` of an `f64`, a `brif`
with float edge arguments, a `jump` with a float argument). -/
theorem lowerShapeT_mv : ∃ ctx st0 R gn bl, LowerShapeT fMv (vcOf fMv) ctx st0 R gn bl := by
  obtain ⟨ctx, ranges, st0, bl, hb, hl, -, -, -⟩ := lowerFunction_runT (by native_decide) lowerFunction_mv
  have he := ctxBlOf_eq hb hl
  have hu : ((aliasOf fMv (ctxBlOf fMv).2).map (·.1)).Nodup := by native_decide
  have hwf : (aliasOf fMv (ctxBlOf fMv).2).all
      (fun p => (aliasOf fMv (ctxBlOf fMv).2).all fun q => q.1 != p.2) = true := by native_decide
  rw [he] at hu hwf
  exact ⟨ctx, st0, _, _, bl, lowerShapeT_of_lowerT lowerFunction_mv scopeT_mv
    (by native_decide) hb hl hu (aliasWF_of_flat hwf)⟩

/-- **Witness**: `shapeOkT_completeT` on a float function with a `br_table` and two float
returns. -/
theorem shapeOkT_tb : ∃ ctx ranges st0 bl, buildCtx fTb = .ok (ctx, ranges, st0) ∧
    lowBlocks fTb (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 fTb.blocks st0 fTb.blocks.length =
      some bl ∧
    shapeOkT fTb (vcOf fTb) ctx st0 (gnAt (gnTable st0.nextVreg (aliasOf fTb bl))) bl = true := by
  obtain ⟨ctx, ranges, st0, bl, hb, hl, -, -, -⟩ := lowerFunction_runT (by native_decide) lowerFunction_tb
  have he := ctxBlOf_eq hb hl
  have hu : ((aliasOf fTb (ctxBlOf fTb).2).map (·.1)).Nodup := by native_decide
  have hwf : (aliasOf fTb (ctxBlOf fTb).2).all
      (fun p => (aliasOf fTb (ctxBlOf fTb).2).all fun q => q.1 != p.2) = true := by native_decide
  rw [he] at hu hwf
  exact ⟨ctx, ranges, st0, bl, hb, hl, shapeOkT_completeT lowerFunction_tb scopeT_tb
    (by native_decide) hb hl hu (aliasWF_of_flat hwf)⟩

/-- **Witness**: `LowT.raw_back` on `fMv`'s `brif` block: its code ends in an instruction
targeting the recorded labels. -/
theorem rawBack_mv : ∃ ctx st0 bl RR L t, Spill.LowT fMv (vcOf fMv) ctx st0 bl RR ∧
    bl[0]? = some L ∧ (fixBlock RR (rawBlockT fMv ctx bl 0 fMv.blocks[0]!)).insts.back? = some t ∧
    t.targets = L.targets ∧ L.targets.length = 2 := by
  obtain ⟨ctx, st0, bl, RR, H⟩ := Spill.lowT_of (by native_decide) lowerFunction_mv
  obtain ⟨ranges, hb⟩ := H.hb
  have he := ctxBlOf_eq hb H.hbl
  have hL : ((ctxBlOf fMv).2[0]?.map (·.targets.length)) = some 2 := by native_decide
  rw [he] at hL
  obtain ⟨L, hL0, hlen⟩ := Option.map_eq_some_iff.mp hL
  have hbt := brIdx_of_ok (scopeT_mv.ctxFacts ctx ranges st0 hb).1
  obtain ⟨t, hback, -, hnt, -⟩ := H.raw_back scopeT_mv hbt (B := fMv.blocks[0]!) (by native_decide) hL0
  exact ⟨ctx, st0, bl, RR, L, t, H, hL0, hback, (hnt (by native_decide)).1, hlen⟩

/-- **Witness**: `LowT.raw_back` on `fTb`'s float `return` block: its code ends in an
instruction without successors. -/
theorem rawBack_tb : ∃ ctx st0 bl RR t, Spill.LowT fTb (vcOf fTb) ctx st0 bl RR ∧
    (fixBlock RR (rawBlockT fTb ctx bl 1 fTb.blocks[1]!)).insts.back? = some t ∧ t.targets = [] := by
  obtain ⟨ctx, st0, bl, RR, H⟩ := Spill.lowT_of (by native_decide) lowerFunction_tb
  obtain ⟨ranges, hb⟩ := H.hb
  have he := ctxBlOf_eq hb H.hbl
  have hL : ((ctxBlOf fTb).2[1]?.map (·.targets)) = some [] := by native_decide
  rw [he] at hL
  obtain ⟨L, hL1, hnil⟩ := Option.map_eq_some_iff.mp hL
  have hbt := brIdx_of_ok (scopeT_tb.ctxFacts ctx ranges st0 hb).1
  obtain ⟨t, hback, -, hnt, -⟩ := H.raw_back scopeT_tb hbt (B := fTb.blocks[1]!) (by native_decide) hL1
  exact ⟨ctx, st0, bl, RR, t, H, hback, by rw [(hnt (by native_decide)).1, hnil]⟩

/-- **Witness**: `lowerCheckT_complete` on a float function outside subset E. -/
theorem lowerCheckT_mv : lowerCheckT fMv (vcOf fMv) = true :=
  lowerCheckT_complete (dominated_of (by native_decide)) scopeT_mv lowerFunction_mv

/-- **Witness**: `lowerCheckT_complete` on a float `br_table` function. -/
theorem lowerCheckT_tb : lowerCheckT fTb (vcOf fTb) = true :=
  lowerCheckT_complete (dominated_of (by native_decide)) scopeT_tb lowerFunction_tb

-- … and the integer validator rejects both
#guard !lowerCheck fMv (vcOf fMv) && !lowerCheck fTb (vcOf fTb)

/-- An integer `call` between float values (the outgoing area, `callOut_runTermT`). -/
def fCall : Clif.Function := fnOfText
  "function %c(f64, i64) -> f64 {
    fn0 = %g(i64) -> i64
block0(v0: f64, v1: i64):
    v2 = call fn0(v1)
    v3 = bitcast.f64 v2
    v4 = select v1, v0, v3
    return v4
}
"

#guard Compile.functionET fCall && !Compile.functionE fCall
#guard (lowerFunction fCall).toBool

theorem lowerFunction_call : lowerFunction fCall = .ok (vcOf fCall) := by
  have hok : (lowerFunction fCall).toBool = true := by native_decide
  unfold vcOf
  cases h : lowerFunction fCall with
  | error e => rw [h] at hok; cases hok
  | ok vc => rfl

/-- `fCall` is in the typed lowering's input conditions. -/
theorem scopeT_call : LowerScopeT fCall where
  subsetT := by native_decide
  nonempty := by native_decide
  noEntryPred := by native_decide
  ctxFacts := by
    intro ctx ranges st0 hb
    have h : (match buildCtx fCall with
        | .ok (c, _, _) => brIdxOk fCall c && ctxOkT fCall c
        | .error _ => false) = true := by native_decide
    rw [hb] at h
    simp only [Bool.and_eq_true] at h
    exact ⟨h.1, (ctxOkT_sound h.2).addr64⟩
  tryRet := by
    have h : fCall.blocks.all (fun B => !B.term.isTry) = true := by native_decide
    intro B hB et ht
    have := List.all_eq_true.mp h B hB
    rcases ht with ⟨fn, args, he⟩ | ⟨c, args, he⟩ <;> rw [he] at this <;> cases this
  stackLayout := by
    have h : fCall.blocks.all (fun B => B.body.all fun st => match st.inst with
        | .call fn _ => (fCall.extern? fn).all (stackLayoutOk ·.sig)
        | _ => true) = true := by native_decide
    have h2 : fCall.blocks.all (fun B => !B.term.isTry) = true := by native_decide
    refine ⟨fun B hB st hst fn args e hi he => ?_, fun B hB fn args et e ht _ => ?_⟩
    · have := List.all_eq_true.mp (List.all_eq_true.mp h B hB) st hst
      rw [hi] at this
      simpa [he] using this
    · have := List.all_eq_true.mp h2 B hB
      rw [ht] at this; cases this
  indStackLayout := by
    have h : (Backend.indSigs fCall).all (fun s => stackLayoutOk s) = true := by native_decide
    exact fun s hs => List.all_eq_true.mp h s hs

/-- **Witness**: `lowerCheckT_complete` on a float function with an integer `call`. -/
theorem lowerCheckT_call : lowerCheckT fCall (vcOf fCall) = true :=
  lowerCheckT_complete (dominated_of (by native_decide)) scopeT_call lowerFunction_call

#guard !lowerCheck fCall (vcOf fCall)

end FloatTermT
