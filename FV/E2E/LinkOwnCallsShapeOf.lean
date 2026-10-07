import FV.E2E.LinkOwnCallsRun
import FV.E2E.LinkArm

/-!
# The operands and the code of a lowered call

`shapeOf_gen`: the call `gen_call_args`/`gen_call_rets` build has operands `ShapeOf` the
registers `callRegs` of the signature. `emit_bl`, `emit_got`: the code of a `call` rule (the
stores of the stack-passed arguments, the GOT load, the call).
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Isle Isle.Interp Isle.Aarch64

theorem regPairsOf_snd : ∀ (la : List (ArgLoc × Nat)) (bytes : List Nat), la.length ≤ bytes.length →
    (regPairsOf (la.zip bytes)).map (·.2) =
      la.filterMap fun q => match q.1 with
        | .reg r => some r
        | .stack _ => none
  | [], _, _ => by simp [regPairsOf]
  | _ :: _, [], h => by simp at h
  | ((.reg r), a) :: la, b :: bytes, h => by
    have := regPairsOf_snd la bytes (by simp at h; omega)
    simp only [regPairsOf, List.zip_cons_cons, List.filterMap_cons] at this ⊢
    simp [this]
  | ((.stack o), a) :: la, b :: bytes, h => by
    have := regPairsOf_snd la bytes (by simp at h; omega)
    simp only [regPairsOf, List.zip_cons_cons, List.filterMap_cons] at this ⊢
    simp [this]

/-- **The operands of a call of `s`** built by `gen_call_args`/`gen_call_rets`: `ShapeOf` the
registers `callRegs s args`. -/
theorem shapeOf_gen {s : Clif.Signature} {locs : List ArgLoc} {S : Nat}
    (hl : sigArgLocs s = .ok (locs, S)) {bytes : List Nat} (hb : sigParamBytes s = .ok bytes)
    (args : List Nat) (d : CallDest) (b k : Nat) :
    ShapeOf (callRegs s args)
      ⟨d, retPairs (regPairsOf ((locs.zip args).zip bytes)), callDefs (outDefs b k)⟩ := by
  have hlocs : locsOf s = locs := by simp [locsOf, hl]
  have hbl := sigParamBytes_length hb
  refine ⟨_, _, rfl, rfl, ?_, ?_⟩
  · rw [regPairsOf_snd _ _ ?_]
    · unfold callRegs
      rw [hlocs]
      congr 1
    · rcases locsOf_length s with h | h
      · rw [hlocs] at h
        simp only [List.length_zip, h, hbl]
        omega
      · rw [hlocs] at h
        simp [h]
  · simp [outDefs, Function.comp_def]

/-- The code of `bl`/`blr` of a register: stores, then the call. -/
theorem emit_bl {st sa st' : LState} (E : List (Nat × Nat × Nat)) (c : CallInfo)
    (h1 : sa.emitted = st.emitted ++ (E.map argStore).toArray) (h2 : st' = sa.emit (.call c)) :
    st'.emitted = st.emitted ++ (E.map argStore ++ [] ++ [MInst.call c]).toArray := by
  subst h2; simp [LState.emit, h1]

/-- The code of `loadExtNameGot t name; blr t`: stores, the GOT load, then the call. -/
theorem emit_got {st sa sb sc st' : LState} (E : List (Nat × Nat × Nat)) (t : Nat) (nm : String)
    (c : CallInfo) (h1 : sa.emitted = st.emitted ++ (E.map argStore).toArray)
    (h2 : sb = sa.emit (.loadExtNameGot (.vreg t .int) nm)) (h3 : sc.emitted = sb.emitted)
    (h4 : st' = sc.emit (.call c)) :
    st'.emitted = st.emitted ++
      (E.map argStore ++ [MInst.loadExtNameGot (.vreg t .int) nm] ++ [MInst.call c]).toArray := by
  subst h4 h2; simp [LState.emit, h3, h1]

end E2E.LinkCheck
