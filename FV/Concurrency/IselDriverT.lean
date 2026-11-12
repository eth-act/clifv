import FV.Backend.Proof.LowerSim

/-!
# The driver hypothesis without extern-only calls (T2j #473, calls at layer 2)

`Driver.DriverHyp` assumes that every `call` statement calls an extern (`ext`): the
single-threaded simulation runs a call as one CLIF step. Layer 2 with interference never steps a
call (a call of a program function pauses the activation, `IselCall`), so its lemmas need the
other facts only:

* **`DriverHypT`**: `DriverHyp` without `ext`; `DriverHyp.toT`;
* `DriverHypT.blow`, `enter_matchT`, `enter_match_brT`: `DriverHyp.blow`, `enter_match`,
  `enter_match_br` on it (their proofs use the shape and the certificate only).
-/

namespace Concurrency

open Backend Backend.Proof Backend.Proof.Driver

/-- **`DriverHyp` without extern-only calls** (module doc). -/
structure DriverHypT (f : Clif.Function) (vc : VCode) (ctx : Ctx) (st0 : LState) (R : Reg → Reg)
    (gn : Nat → Nat) (bl : List BLow) (A : Nat → Nat → List Clif.ValueId) {W : Type}
    (sem : ISem CV W) (MR : MemRelTW W) (env : Clif.Env) (p : Clif.Program) : Prop where
  shape : LowerShape f vc ctx st0 R gn bl
  cert : Cert f ctx st0 gn bl A
  dsem : DriverSemG sem
  insts : InstCalls f sem MR env p
  terms : TermCalls sem MR
  indSig : ∀ B ∈ f.blocks, ∀ st ∈ B.body, IndSigOk f (indSigs f) st.inst
  subE : Compile.functionE f = true
  brIdx : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term
  noTail : ∀ B ∈ f.blocks, ∀ fn args, B.term ≠ .returnCall fn args
  tries : ∃ out, TryCalls f sem MR env p out ∧ TryStack f out
  tryExt : ∀ B ∈ f.blocks, ∀ fn args et, B.term = .tryCall fn args et →
    ∀ e, f.extern? fn = some e → p.func? e.name = none
  tryInd : TryIndCalls sem MR env p (indSigs f)
  tryIndSig : ∀ B ∈ f.blocks, ∀ c args et s, B.term = .tryCallIndirect c args et →
    f.sigDecls.lookup et.sig = some s → s ∈ indSigs f
  cfg : ∃ ss ps, vc.cfg = .ok (ss, ps)
  entryLocs : (locsOf f.sig).length = f.sig.params.length ∧ ∃ bytes, sigParamBytes f.sig = .ok bytes

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {W : Type}
  {sem : ISem CV W} {MR : MemRelTW W} {env : Clif.Env} {p : Clif.Program}
  {slots : List (Clif.SlotId × Nat)}

/-- `DriverHyp` gives `DriverHypT`. -/
theorem _root_.Backend.Proof.Driver.DriverHyp.toT (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p) :
    DriverHypT f vc ctx st0 R gn bl A sem MR env p :=
  ⟨H.shape, H.cert, H.dsem, H.insts, H.terms, H.indSig, H.subE, H.brIdx, H.noTail, H.tries,
    H.tryExt, H.tryInd, H.tryIndSig, H.cfg, H.entryLocs⟩

theorem DriverHypT.blow (H : DriverHypT f vc ctx st0 R gn bl A sem MR env p) {bi : Nat}
    {B : Clif.Block} (hB : f.blocks[bi]? = some B) : ∃ L, bl[bi]? = some L := by
  have hlt : bi < f.blocks.length := (List.getElem?_eq_some_iff.mp hB).1
  exact ⟨bl[bi]'(by rw [H.shape.len]; exact hlt), List.getElem?_eq_getElem _⟩

/-- **Entering a successor block** (`Driver.enter_match` on `DriverHypT`). -/
theorem enter_matchT (H : DriverHypT f vc ctx st0 R gn bl A sem MR env p)
    {s : Clif.State} {b : Nat} {B : Clif.Block} (hB : f.blocks[b]? = some B)
    (hcall : s.callers = []) (hfunc : s.frame.func = f) (hslots : s.frame.slots = slots)
    {ρ : Nat → CV} (hheld : Held gn (A b B.body.length) ρ s.frame)
    (hcons : DFGCons ctx (restrict s.frame (A b B.body.length)))
    {bc : Clif.BlockCall} (hbc : bc.block ∈ edgeIds B.term) {tl : Nat}
    (htl : blockIdx? f bc.block = some tl)
    {fr2 : Clif.Frame} (hent : Clif.enterBlock s.frame bc = .ok fr2) {ρ₂ : Nat → CV}
    (hρ₂ : ∀ x ∈ A b B.body.length, ρ₂ (gn x) = ρ (gn x)) {xs : List Nat}
    (hxl : xs.length = bc.args.length)
    (hxv : ∀ (m : Nat) a v x, bc.args[m]? = some a → s.frame.regs a = some v → xs[m]? = some x →
      VHolds v (ρ₂ x))
    {w₂ : W} (hmr : MR slots s.mem w₂) :
    ∃ TB, f.blocks[tl]? = some TB ∧ bc.args.length = TB.params.length ∧ tl ≠ 0 ∧
      Match f ctx R gn bl A MR slots { s with frame := fr2 }
        ⟨tl, 0, parCopyEnv ρ₂ (TB.params.map (·.1)) xs, w₂⟩ := by
  obtain ⟨TB, args, regs, hTBf, hargs, hty, hset, rfl⟩ := enterBlock_spec hent
  rw [hfunc] at hTBf
  have hTB := blockIdx_block htl hTBf
  have hne0 : tl ≠ 0 := fun e => H.cert.noEntry b B hB bc.block hbc (e ▸ htl)
  obtain ⟨hl1, hgm⟩ := getMany_spec hargs
  have hl2 := setMany_length hset
  have hlen : bc.args.length = TB.params.length := by simp at hl2; omega
  obtain ⟨-, -, hedge⟩ := H.cert.term b B _ hB (H.blow hB).choose_spec
  obtain ⟨hnd, hpA, hA0⟩ := hedge bc.block hbc tl TB htl hTB
  have hTBmem : TB ∈ f.blocks := List.mem_of_getElem? hTB
  have hpos : pos f R bl tl 0 = 0 := by
    simp [pos, pre]
    cases tl with
    | zero => exact absurd rfl hne0
    | succ n => rfl
  refine ⟨TB, hTB, hlen, hne0, hcall, hfunc, hslots, hmr, TB, 0, hTB, rfl, Nat.zero_le _,
    by simp, hpos.symm, ?_, ?_⟩
  · intro x hx
    rcases hA0 x hx with ⟨hxp, -⟩ | ⟨hxp, hxA, hgx⟩
    · obtain ⟨m, v, hxm, hvm, hrv⟩ := setMany_mem hset hnd x hxp
      refine ⟨v, hrv, ?_⟩
      have hm : m < bc.args.length := by
        have := (List.getElem?_eq_some_iff.mp hxm).1; simp at this; omega
      have ha := List.getElem?_eq_getElem hm
      obtain ⟨v', hv', hvm'⟩ := hgm m _ ha
      rw [hvm] at hvm'; cases hvm'
      have hgp : gn x = x := by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hxp
        exact H.shape.params TB hTBmem q hq
      have hxm' : xs[m]? = some xs[m] := List.getElem?_eq_getElem (by omega)
      show VHolds v (parCopyEnv ρ₂ (TB.params.map (·.1)) xs (gn x))
      rw [hgp, parCopyEnv_param hnd (by simp; omega) m hxm hxm']
      exact hxv m _ v _ ha hv' hxm'
    · obtain ⟨v, hv, hh⟩ := hheld x hxA
      refine ⟨v, by show regs x = some v; rw [setMany_other hset hxp]; exact hv, ?_⟩
      show VHolds v (parCopyEnv ρ₂ (TB.params.map (·.1)) xs (gn x))
      rw [parCopyEnv_other hgx, hρ₂ x hxA]
      exact hh
  refine ⟨?_, ?_⟩
  rotate_left
  · intro x t v ht hv
    have hx0 : x ∈ A tl 0 := restrict_regs_isSome (by rw [hv]; rfl)
    have hv' : regs x = some v := by
      have := restrict_regs_of_mem (fr := { s.frame with regs, body := TB.body, term := TB.term }) hx0
      rw [this] at hv; exact hv
    by_cases hxp : x ∈ TB.params.map (·.1)
    · obtain ⟨q, hq, rfl, hqt⟩ := setMany_param_ty hset hnd hty hxp hv'
      rw [H.cert.paramTy TB hTBmem q hq] at ht
      rw [hqt]; exact Option.some.inj ht
    · rcases hA0 x hx0 with ⟨hxp', -⟩ | ⟨-, hxA, -⟩
      · exact absurd hxp' hxp
      · refine hcons.2 x t v ht ?_
        rw [restrict_regs_of_mem hxA, ← setMany_other hset hxp]
        exact hv'
  · intro x d info cl v hd hinfo hcl hp hv
    have hx0 : x ∈ A tl 0 := restrict_regs_isSome (by rw [hv]; rfl)
    have hv' : regs x = some v := by
      have := restrict_regs_of_mem (fr := { s.frame with regs, body := TB.body, term := TB.term }) hx0
      rw [this] at hv; exact hv
    rcases hA0 x hx0 with ⟨-, hdn⟩ | ⟨hxp, hxA, -⟩
    · rw [hdn] at hd; cases hd
    · have hvx : (restrict s.frame (A b B.body.length)).regs x = some v := by
        rw [restrict_regs_of_mem hxA, ← setMany_other hset hxp]; exact hv'
      obtain ⟨vals0, hev, hlk⟩ := hcons.1 x d info cl v hd hinfo hcl hp hvx
      refine ⟨vals0, fun cm => ?_, hlk⟩
      rw [← hev cm]
      refine evalInst_congr ?_ ?_ cm cl ?_
      · rfl
      · rfl
      intro y hy
      have hy0 := H.cert.closed tl 0 x d info cl hx0 hd hinfo hcl hp y hy
      have hyA := H.cert.closed b B.body.length x d info cl hxA hd hinfo hcl hp y hy
      have hyp : y ∉ TB.params.map (·.1) := hpA x hx0 hxp d info cl hd hinfo hcl y hy
      rw [restrict_regs_of_mem hy0, restrict_regs_of_mem hyA]
      exact setMany_other hset hyp

/-- **Entering a branch's successor** (`Driver.enter_match_br` on `DriverHypT`). -/
theorem enter_match_brT (H : DriverHypT f vc ctx st0 R gn bl A sem MR env p)
    {s : Clif.State} {b : Nat} {B : Clif.Block} (hB : f.blocks[b]? = some B)
    (hcall : s.callers = []) (hfunc : s.frame.func = f) (hslots : s.frame.slots = slots)
    {ρ : Nat → CV} (hheld : Held gn (A b B.body.length) ρ s.frame)
    (hcons : DFGCons ctx (restrict s.frame (A b B.body.length)))
    {bc : Clif.BlockCall} (hbc : bc ∈ dests B.term) {tl : Nat} (htl : blockIdx? f bc.block = some tl)
    {fr2 : Clif.Frame} (hent : Clif.enterBlock s.frame bc = .ok fr2) {ρ₂ : Nat → CV}
    (hρ₂ : ∀ x ∈ A b B.body.length, ρ₂ (gn x) = ρ (gn x)) {w₂ : W}
    (hmr : MR slots s.mem w₂) :
    ∃ TB, f.blocks[tl]? = some TB ∧ bc.args.length = TB.params.length ∧ tl ≠ 0 ∧
      Match f ctx R gn bl A MR slots { s with frame := fr2 }
        ⟨tl, 0, parCopyEnv ρ₂ (TB.params.map (·.1)) (bc.args.map gn), w₂⟩ := by
  refine enter_matchT H hB hcall hfunc hslots hheld hcons (mem_edgeIds_of_dests hbc) htl hent hρ₂
    (by simp) (fun m a v x ha hv hx => ?_) hmr
  have haA : a ∈ A b B.body.length :=
    (H.cert.term b B _ hB (H.blow hB).choose_spec).1 _
      (termArgs_abiTerm (args_termArgs hbc _ (List.mem_of_getElem? ha)))
  obtain ⟨v', hv', hh⟩ := hheld a haA
  rw [hv] at hv'; cases hv'
  simp only [List.getElem?_map, ha, Option.map_some, Option.some.injEq] at hx
  subst hx
  rw [hρ₂ a haA]; exact hh

end

end Concurrency
