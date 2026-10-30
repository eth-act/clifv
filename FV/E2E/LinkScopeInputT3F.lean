import FV.E2E.LinkScopeDefsT
import FV.Backend.Proof.IselPrgDriverTF

/-!
# The decider-free input chain over the float scope: `lowerFunction` (S11f, #35)

The first link of the input-scope chain (`LinkScopeInputT3.lean`) over the float scope
`Compile.functionETF` (the typed movement scope with the S11f float arithmetic, rounding,
conversions and scalar `fcmp`, their integer positions `intOperandsF` and float positions
`floatOperands`):

* `lowerScopeTFB` decides `LowerScopeTF` (`lowerScopeTF_of`): `lowerScopeTB` with
  `Compile.functionETF`; `lowerScopeTFB_of_lowerScopeTB`: it widens `lowerScopeTB`;
* `lowerFunction_ok_inT3F`: **`lowerFunction` succeeds** on every function meeting the decided
  input conditions of `lowerFunction_ok_T3` with `lowerScopeTFB` for `lowerScopeTB`
  (`Prg.lowerFunction_ok_inputTF`). No conjunct runs `lowerFunction`.

`lowerScopeTB`, `fnScopeInTB3` and their theorems are unchanged.
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver

/-- `LowerScopeTF f`, decided (`lowerScopeTF_of`): `lowerScopeTB` with `Compile.functionETF`. -/
def lowerScopeTFB (f : Clif.Function) : Bool :=
  Compile.functionETF f && !f.blocks.isEmpty &&
  f.blocks.all (fun B => (succIds B.term).all fun b => blockIdx? f b != some 0) &&
  (match buildCtx f with
    | .error _ => true
    | .ok (ctx, _, _) => brIdxOk f ctx &&
      ctx.insts.toList.all fun info => match info.clif with
        | some inst => match memAddr? inst with
          | some x => decide (ctx.valueType? x = some (.int 64))
          | none => true
        | none => true) &&
  f.blocks.all (fun B => match B.term with
    | .tryCall _ _ et | .tryCallIndirect _ _ et => match f.sigDecls.lookup et.sig with
      | some sig => et.normal.args.all fun
        | .ret i => decide (i < sig.returns.length)
        | _ => true
      | none => true
    | _ => true) &&
  f.blocks.all (fun B => B.body.all fun st => match st.inst with
    | .call fn _ => match f.extern? fn with
      | some e => stackLayoutOk e.sig
      | none => true
    | _ => true) &&
  f.blocks.all fun B => match B.term with
    | .tryCall fn _ _ => match f.extern? fn with
      | some e => stackLayoutOk e.sig
      | none => true
    | _ => true

/-- **`lowerScopeTFB` decides `LowerScopeTF`.** -/
theorem lowerScopeTF_of {f : Clif.Function} (h : lowerScopeTFB f = true) : LowerScopeTF f := by
  simp only [lowerScopeTFB, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq,
    Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨hE, hne⟩, hent⟩, hctx⟩, htry⟩, hcall⟩, htc⟩ := h
  refine ⟨hE, hne, hent, fun ctx ranges st0 hb => ?_, fun B hB et het sig hsig i hi => ?_,
    ⟨fun B hB st hst fn args e hi he => ?_, fun B hB fn args et e ht he => ?_⟩⟩
  · rw [hb] at hctx
    simp only [Bool.and_eq_true, List.all_eq_true] at hctx
    refine ⟨hctx.1, fun ii info inst x hi hc hm => ?_⟩
    have := hctx.2 info (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi))
    simp only [hc, hm, decide_eq_true_eq] at this
    exact this
  · have := htry B hB
    rcases het with ⟨fn, args, ht⟩ | ⟨c, args, ht⟩ <;>
    · simp only [ht, hsig, List.all_eq_true] at this
      have := this _ hi
      simpa using this
  · have := hcall B hB st hst
    simp only [hi, he] at this
    exact this
  · have := htc B hB
    simp only [ht, he] at this
    exact this

/-- **`lowerScopeTFB` widens `lowerScopeTB`.** -/
theorem lowerScopeTFB_of_lowerScopeTB {f : Clif.Function} (h : lowerScopeTB f = true) :
    lowerScopeTFB f = true := by
  unfold lowerScopeTB at h
  unfold lowerScopeTFB
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨hE, hne⟩, hent⟩, hctx⟩, htry⟩, hcall⟩, htc⟩ := h
  exact ⟨⟨⟨⟨⟨⟨Compile.functionETF_of_functionET hE, hne⟩, hent⟩, hctx⟩, htry⟩, hcall⟩, htc⟩

/-- **`lowerFunction` succeeds on the decided input conditions over the float scope**
(`Prg.lowerFunction_ok_inputTF`): `lowerFunction_ok_T3`'s conditions with `lowerScopeTFB` (the
float scope `Compile.functionETF`) for `lowerScopeTB`. -/
theorem lowerFunction_ok_inT3F {g : Clif.Function} (habi : sigAbiOk g.sig = true)
    (hd : dominatedB g = true) (hs : lowerScopeTFB g = true) (har : Spill.arityOkB g = true)
    (hent : Spill.entryParamsB g = true) (hw : extendsWidenB g = true)
    (hdrv : driverInB g = true) (hin : Prg.iselInB g = true) :
    ∃ vc, lowerFunction g = .ok vc :=
  Prg.lowerFunction_ok_inputTF habi hd (lowerScopeTF_of hs) har hent hw hdrv hin

end E2E.LinkCheck
