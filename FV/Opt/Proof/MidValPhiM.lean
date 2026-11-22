import FV.Opt.Proof.ConstPhiSimU
import FV.Opt.Proof.MidValWf
import FV.Opt.MidValFold

/-!
# Constant-phi removal in a function with a `call_indirect` (#1119, removed block parameters)

`Opt.ConstPhi.cpOk` and the validator's `Opt.MidVal.phiOk` start with `Opt.check`, whose
well-formedness `Opt.Wf` gives no result types to a `call_indirect` (`Opt.Wf.noCI`: a
well-formed function has none), so the block parameters Cranelift's `remove_constant_phis`
removes in a function with a `call_indirect` stayed, and the pair was rejected (870 pairs of
the #1119 corpus). `Opt.MidVal.phiOkM` is `phiOk` with the validator's well-formedness check
`Opt.MidVal.wfCheck` (`call_indirect` result types from the function's signature declarations,
`sigDeclOf`; facts `Opt.MidVal.WfM`). Here, under new names (nothing on main restated):

* `CpFactsM`: `ConstPhi.CpFacts` with `WfM` in place of `Wf`; `phiOkM_facts` gives it.
* The simulation of `FV/Opt/Proof/ConstPhiSim.lean` and `ConstPhiSimU.lean` (relation
  `ConstPhi.CR`, unchanged) from `CpFactsM`: the same proofs through the `WfM` lemmas
  (`…M` names), and the `call_indirect` step, which `Wf` made vacuous: **`CRel.ciM`** (the same
  signature, the renamed callee and arguments read the same values, the results bound alike;
  their types from the signature declarations, `WfM.inv_results`); **`CR.isSimWUM`**.
* **`phiOkM_simU`**: `phiOkM f sol = true → FunSimU f (ConstPhi.apply f sol)`.
-/

namespace Opt.ConstPhi

open Clif Opt

/-- `CpFacts` with the validator's well-formedness facts `WfM` (module doc). -/
structure CpFactsM (m : Std.HashMap ValueId ValueId) (f : Function) (D : WfData) : Prop where
  wf : MidVal.WfM f D
  key : ∀ x, m.contains x = true → ∃ bp dv t, D.dm x = some (bp, 0) ∧ bp ≠ 0 ∧
    m.contains (rename m x) = false ∧ D.dm (rename m x) = some (dv, t) ∧ dv ≠ bp ∧
    Anc D.idom dv bp
  edge : ∀ (i : Nat) (b : Block), f.blocks[i]? = some b → ∀ e ∈ edges b.term, ∀ (j : Nat) (db : Block),
    D.index e.1 = some j → f.blocks[j]? = some db → db.params.length = e.2.length ∧
    ∀ (n : Nat) p a, db.params[n]? = some p → e.2[n]? = some a → m.contains p.1 = true →
      ∃ x, a = some x ∧ rename m x = rename m p.1

/-! ## Where renamed values are defined -/

section
variable {m : Std.HashMap ValueId ValueId} {f : Function} {D : WfData} (hF : CpFactsM m f D)
include hF

/-- A statement result is not a removed parameter. -/
theorem rename_resultM {bi k : Nat} {b : Block} {st : Stmt} {v : ValueId}
    (hb : f.blocks[bi]? = some b) (hst : b.body[k]? = some st) (hv : v ∈ st.results) :
    rename m v = v := by
  cases hc : m.contains v
  · exact rename_of_not hc
  · obtain ⟨bp, -, -, hp, -⟩ := hF.key v hc
    rw [MidVal.WfM.site_result hF.wf hb hst hv] at hp
    simp at hp

/-- The renaming of an available value is not a result of the statement at that point: a
removed parameter's solution is defined in a strict dominator of the parameter's block. -/
theorem rename_not_resultM {bi k : Nat} {b : Block} {st : Stmt} {v : ValueId}
    (hb : f.blocks[bi]? = some b) (hst : b.body[k]? = some st) (hv : Avail D bi k v) :
    rename m v ∉ st.results := by
  cases hc : m.contains v
  · rw [rename_of_not hc]; exact MidVal.WfM.avail_not_result hF.wf hb hst hv
  · obtain ⟨bp, dv, t, hp, -, -, hd, hne, ha⟩ := hF.key v hc
    intro hr
    rw [MidVal.WfM.site_result hF.wf hb hst hr] at hd
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, -⟩ := hd
    obtain ⟨d0, t0, hv0, hva⟩ := hv
    rw [hp] at hv0
    simp only [Option.some.injEq, Prod.mk.injEq] at hv0
    obtain ⟨rfl, rfl⟩ := hv0
    rcases hva with ⟨he, -⟩ | ⟨hne2, ha2⟩
    · exact hne he.symm
    · exact hne2 (Anc.antisymm hF.wf.rank ha2 ha)

/-- The renaming of a value available at the start of block `j`, unless it is a kept parameter
of `j`, is not a parameter of `j`. -/
theorem rename_not_paramM {j : Nat} {b2 : Block} {v : ValueId} (hj : f.blocks[j]? = some b2)
    (hv : Avail D j 0 v) (hk : D.dm v = some (j, 0) → m.contains v = true) :
    rename m v ∉ b2.params.map (·.1) := by
  intro hm
  obtain ⟨p, hp, hpv⟩ := List.mem_map.1 hm
  have hsite := MidVal.WfM.site_param hF.wf hj hp
  rw [hpv] at hsite
  cases hc : m.contains v
  · rw [rename_of_not hc] at hsite
    rw [hk hsite] at hc; cases hc
  · obtain ⟨bp, dv, t, hp0, -, -, hd, hne, ha⟩ := hF.key v hc
    rw [hsite] at hd
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, -⟩ := hd
    obtain ⟨d0, t0, hv0, hva⟩ := hv
    rw [hp0] at hv0
    simp only [Option.some.injEq, Prod.mk.injEq] at hv0
    obtain ⟨rfl, rfl⟩ := hv0
    rcases hva with ⟨he, -⟩ | ⟨hne2, ha2⟩
    · exact hne he.symm
    · exact hne2 (Anc.antisymm hF.wf.rank ha2 ha)

/-- The renaming of an available value is below the rewritten function's fresh value. -/
theorem rename_ltM {bi k : Nat} {v : ValueId} (hv : Avail D bi k v) :
    rename m v < (cpFun m f).freshValue := by
  obtain ⟨d, t, hd, -⟩ := hv
  cases hc : m.contains v
  · rw [rename_of_not hc]
    exact lt_cpFun_freshValue (hF.wf.sitesRev _ _ hd) hc
  · obtain ⟨-, dv, t', -, -, hnc, hd', -⟩ := hF.key v hc
    exact lt_cpFun_freshValue (hF.wf.sitesRev _ _ hd') hnc

end

section
variable {m : Std.HashMap ValueId ValueId} {f : Function} {D : WfData} (hF : CpFactsM m f D)
  {syms : String → Option Nat}
include hF

/-- A statement other than a call steps in lock-step. -/
theorem CRel.stmtM {fr fr' : Frame} {bi k : Nat} {mm : Mem} {s : Stmt} {ss : List Stmt}
    (h : CRel m f D syms fr fr' bi k) (hm : mm.symbols = syms) (hs : fr.body = s :: ss)
    (hnc : ∀ fn args, s.inst ≠ .call fn args) :
    (∀ fr1 m1, lstep fr mm = .next fr1 m1 → ∃ fr1', lstep fr' mm = .next fr1' m1 ∧
      CRel m f D syms fr1 fr1' bi (k + 1)) ∧
    (∀ c, lstep fr mm = .trap c → lstep fr' mm = .trap c) := by
  obtain ⟨b, hbi, hbody, -, -⟩ := h.inv.block
  have hs0 := hs
  rw [hbody] at hs
  obtain ⟨hsk, -, -⟩ := drop_eq_cons hs
  have ht : fr'.body = renStmt (rename m) s :: ss.map (renStmt (rename m)) := by
    rw [h.body, hs0]; rfl
  have hops : ∀ x ∈ operands s.inst, fr'.regs (rename m x) = fr.regs x :=
    fun x hx => h.agree x (hF.wf.uses bi b hbi k s hsk x hx)
  have hev := evalInst_rename (mem := mm) h.globals h.externs h.slots hops
  have hnc' := mapOperands_not_call (σ := rename m) hnc
  rw [lstep_inst hs0 hnc, lstep_inst ht hnc']
  refine ⟨fun fr1 m1 hl => ?_, fun c hl => ?_⟩
  · cases he : evalInst fr mm s.inst with
    | trap c => rw [he] at hl; cases hl
    | stuck msg => rw [he] at hl; cases hl
    | ok p =>
      obtain ⟨vals, m1'⟩ := p
      rw [he] at hl
      simp only [LRes.ofRes] at hl
      split at hl
      · rename_i regs hset
        cases hl
        have he' := Res.norm_eq_ok hev he
        obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs) (xs := s.results) (vs := vals)
          (setMany_spec hset).1
        simp only [renStmt] at he' ⊢
        rw [he']
        simp only [LRes.ofRes, hset']
        refine ⟨_, rfl, ⟨?_, h.func, rfl, h.term, h.slots, ?_⟩⟩
        · exact MidVal.WfM.inv_results hF.wf h.inv hs0 (fun ts0 h0 => evalInst_types he h0)
            (fun hp => by
              obtain ⟨-, a, rfl, ha⟩ := evalInst_pure hp he
              exact ⟨a, rfl, by rw [evalNode_mem (m := mm) hp (by rw [hm]; rfl)]; exact ha⟩) hset
        · intro v hv
          rcases MidVal.WfM.avail_succ hF.wf hbi hsk hv with hr | hv'
          · rw [rename_resultM hF hbi hsk hr]
            exact (setMany_same hset hset' v hr).symm
          · show regs' (rename m v) = regs v
            rw [((setMany_spec hset').2 _).1 (rename_not_resultM hF hbi hsk hv'),
              ((setMany_spec hset).2 _).1 (MidVal.WfM.avail_not_result hF.wf hbi hsk hv'), h.agree v hv']
      · cases hl
  · cases he : evalInst fr mm s.inst with
    | ok p => rw [he] at hl; obtain ⟨_, _⟩ := p; simp only [LRes.ofRes] at hl; split at hl <;> cases hl
    | stuck msg => rw [he] at hl; cases hl
    | trap c' =>
      rw [he] at hl; cases hl
      simp only [renStmt]
      rw [Res.norm_eq_trap hev he]; rfl

/-- A call: the same callee and arguments; the continuations are related. -/
theorem CRel.callM {fr fr' : Frame} {bi k : Nat} {mm : Mem} {ext : ExtFunc} {vals : List Val}
    {rs : List ValueId} {rest : List Stmt} (h : CRel m f D syms fr fr' bi k)
    (hl : lstep fr mm = .call ext vals rs rest) :
    lstep fr' mm = .call ext vals rs (rest.map (renStmt (rename m))) ∧
      Cont (CR m f D syms) { fr with body := rest } rs
        { fr' with body := rest.map (renStmt (rename m)) } rs (AbiParam.tys ext.sig.returns) := by
  obtain ⟨s, fn, args, hs0, hc, hrs, hca⟩ := lstep_call_inv hl
  subst hrs
  obtain ⟨b, hbi, hbody, -, -⟩ := h.inv.block
  have hs := hs0
  rw [hbody] at hs
  obtain ⟨hsk, -, -⟩ := drop_eq_cons hs
  have ht : fr'.body = renStmt (rename m) s :: rest.map (renStmt (rename m)) := by
    rw [h.body, hs0]; rfl
  have hops : ∀ x ∈ operands s.inst, fr'.regs (rename m x) = fr.regs x :=
    fun x hx => h.agree x (hF.wf.uses bi b hbi k s hsk x hx)
  have hca' := Res.norm_eq_ok (callArgs_rename (σ := rename m) (fr := fr) (fr' := fr') (fn := fn)
    h.externs (fun x hx => hops x (by rw [hc]; exact hx))) hca
  have htc : (renStmt (rename m) s).inst = .call fn (args.map (rename m)) := by
    simp [renStmt, hc, mapOperands]
  refine ⟨by rw [lstep_call ht htc, hca']; rfl, ?_⟩
  intro vs regs hty hset
  obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs) (xs := s.results) (vs := vs)
    (setMany_spec hset).1
  refine ⟨regs', hset', bi, k + 1, ?_, h.func, rfl, h.term, h.slots, ?_⟩
  · have hext : sigOf f fn = some ext.sig := by
      simp only [callArgs, Res.bind_eq_ok, Res.ofOption_eq_ok] at hca
      obtain ⟨e, he, _, _, _, _, hpe⟩ := hca
      simp only [Res.pure_eq_ok, Prod.mk.injEq] at hpe
      obtain ⟨rfl, -⟩ := hpe
      rw [h.inv.func] at he
      simp only [sigOf]
      rw [show f.externs.lookup fn = f.extern? fn from rfl, he]; rfl
    refine MidVal.WfM.inv_results (fr := fr) (st := s) (rest := rest) hF.wf h.inv hs0 (fun ts0 h0 => ?_)
      (fun hp => by rw [hc] at hp; cases hp) hset
    rw [hc, Inst.resultTypes, hext] at h0
    simp only [Option.map_some, Option.some.injEq] at h0
    rw [← h0, hty]; rfl
  · intro v hv
    rcases MidVal.WfM.avail_succ hF.wf hbi hsk hv with hr | hv'
    · rw [rename_resultM hF hbi hsk hr]
      exact (setMany_same hset hset' v hr).symm
    · show regs' (rename m v) = regs v
      rw [((setMany_spec hset').2 _).1 (rename_not_resultM hF hbi hsk hv'),
        ((setMany_spec hset).2 _).1 (MidVal.WfM.avail_not_result hF.wf hbi hsk hv'), h.agree v hv']

end

section
variable {m : Std.HashMap ValueId ValueId} {f : Function} {D : WfData} (hF : CpFactsM m f D)
  {syms : String → Option Nat}
include hF

/-- **Branching**: given the argument values of the source edge, the target edge's arguments
are the kept ones, and each removed position's argument is the value the target holds at its
parameter's renaming, both frames enter the destination at related points. -/
theorem enterAtM {fr fr' fr1 : Frame} {bi k : Nat} (hinv : Inv f D syms fr bi k)
    (hs : fr.body = []) (hfunc : fr'.func = cpFun m f) (hsl : fr'.slots = fr.slots)
    (hagree : ∀ v, Avail D bi k v → fr'.regs (rename m v) = fr.regs v)
    {bc bc' : BlockCall} (hsucc : bc.block ∈ termSuccs fr.term) (he : enterBlock fr bc = .ok fr1)
    (hblk : bc'.block = bc.block)
    (hargs : ∀ vs, fr.getMany bc.args = .ok vs →
      fr'.getMany bc'.args = .ok (filt (keepOf (keepMap m f) bc.block) vs) ∧
      ∀ b2, f.block? bc.block = some b2 → ∀ (n : Nat) p, b2.params[n]? = some p →
        m.contains p.1 = true → fr'.regs (rename m p.1) = vs[n]?) :
    ∃ fr1', enterBlock fr' bc' = .ok fr1' ∧ CR m f D syms fr1 fr1' := by
  obtain ⟨b, hbi, hk, hterm⟩ := inv_atEnd hinv hs
  subst hk
  obtain ⟨j, b2, hj, hb2, hinv1⟩ := MidVal.WfM.inv_enter hF.wf hinv hs hsucc he
  obtain ⟨b2x, args, regs, hb2x, hga, hty, hset, rfl⟩ := enterBlock_ok he
  rw [hinv.func, hb2] at hb2x; cases hb2x
  obtain ⟨hga', hrem⟩ := hargs args hga
  rw [keepOf_block hb2] at hga'
  let P : ValueId → Bool := fun y => !m.contains y
  have hgb : fr'.func.block? bc'.block = some (cpBlock m (keepMap m f) b2) := by
    rw [hfunc, hblk, cpFun_block?, hb2]; rfl
  have hxsf : (cpBlock m (keepMap m f) b2).params.map (·.1) = (b2.params.map (·.1)).filter P := by
    simp only [cpBlock, List.filter_map]; rfl
  have hks : b2.params.map (fun p => !m.contains p.1) = (b2.params.map (·.1)).map P := by
    rw [List.map_map]; rfl
  have hty' : (filt (b2.params.map fun p => !m.contains p.1) args).map (·.ty) =
      (cpBlock m (keepMap m f) b2).params.map (·.2) := by
    rw [← filt_map, hty, filt_filter]; rfl
  have hlen := (setMany_spec hset).1
  obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs)
    (xs := (cpBlock m (keepMap m f) b2).params.map (·.1))
    (vs := filt (b2.params.map fun p => !m.contains p.1) args) (by
      rw [hxsf, hks, length_filt_filter P _ _ hlen])
  have he' := enterBlock_of hgb hga' hty' hset'
  refine ⟨_, he', j, 0, hinv1, hfunc, rfl, rfl, hsl, fun v hv => ?_⟩
  show regs' (rename m v) = regs v
  have hbid : b2.id = bc.block := by obtain ⟨_, _, h0⟩ := MidVal.WfM.block?_index hF.wf hb2; exact h0
  have hnot : ∀ y, y ∈ (cpBlock m (keepMap m f) b2).params.map (·.1) → y ∈ b2.params.map (·.1) := by
    intro y hy
    obtain ⟨p', hp', he'⟩ := List.mem_map.1 hy
    exact List.mem_map.2 ⟨p', (List.mem_filter.1 hp').1, he'⟩
  by_cases hdv : D.dm v = some (j, 0)
  · obtain ⟨b4, p, hb4, hp, hpv⟩ := MidVal.WfM.site_param' hF.wf hdv
    rw [hj] at hb4; cases hb4
    have hvm : v ∈ b2.params.map (·.1) := List.mem_map.2 ⟨p, hp, hpv⟩
    cases hc : m.contains v
    · rw [rename_of_not hc]
      rw [hxsf, hks] at hset'
      exact setMany_filter_eq P _ _ _ _ _ _ hset hset' v hvm (by simp [P, hc])
    · obtain ⟨n, hn, hrv⟩ := ((setMany_spec hset).2 v).2 hvm
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hn
      obtain ⟨q, hq, hqv⟩ := hn
      subst hqv
      rw [((setMany_spec hset').2 _).1 (fun hm => rename_not_paramM hF hj hv (fun _ => hc) (hnot _ hm)),
        hrem b2 hb2 n q hq hc, hrv]
  · have hvp := MidVal.WfM.avail_pred hF.wf hbi hj (by rw [hbid, ← hterm]; exact hsucc) hv hdv
    have hn2 : v ∉ b2.params.map (·.1) := by
      intro hm
      obtain ⟨p, hp, hpv⟩ := List.mem_map.1 hm
      exact hdv (by rw [← hpv]; exact MidVal.WfM.site_param hF.wf hj hp)
    rw [((setMany_spec hset').2 _).1 (fun hm => rename_not_paramM hF hj hv
        (fun h => absurd h hdv) (hnot _ hm)),
      ((setMany_spec hset).2 _).1 hn2, hagree v hvp]

/-- The values the terminator reads hold in the target at their renamings. -/
theorem CRel.termOpsM {fr fr' : Frame} {bi k : Nat} (h : CRel m f D syms fr fr' bi k)
    (hs : fr.body = []) : ∀ x ∈ termOperands fr.term, fr'.regs (rename m x) = fr.regs x ∧
      x < f.freshValue ∧ rename m x < (cpFun m f).freshValue := by
  obtain ⟨b, hbi, hk, hterm⟩ := inv_atEnd h.inv hs
  subst hk
  intro x hx
  rw [hterm] at hx
  have hav := hF.wf.termUses bi b hbi x hx
  exact ⟨h.agree x hav, MidVal.WfM.avail_lt hF.wf hav, rename_ltM hF hav⟩

/-- The arguments of a plain edge (`jump`, `brif`, `br_table`). -/
theorem CRel.plainArgsM {fr fr' : Frame} {bi k : Nat} (h : CRel m f D syms fr fr' bi k)
    (hs : fr.body = []) {bc : BlockCall} (hedge : (bc.block, bc.args.map some) ∈ edges fr.term)
    (hops : ∀ x ∈ bc.args, x ∈ termOperands fr.term) :
    ∀ vs, fr.getMany bc.args = .ok vs →
      fr'.getMany (filterBC (keepMap m f) (mapBlockCall (rename m) bc)).args =
        .ok (filt (keepOf (keepMap m f) bc.block) vs) ∧
      ∀ b2, f.block? bc.block = some b2 → ∀ (n : Nat) p, b2.params[n]? = some p →
        m.contains p.1 = true → fr'.regs (rename m p.1) = vs[n]? := by
  intro vs hvs
  have hT := h.termOpsM hF hs
  obtain ⟨b, hbi, hk, hterm⟩ := inv_atEnd h.inv hs
  refine ⟨?_, fun b2 hb2 n p hp hc => ?_⟩
  · exact getMany_filt _ _ (Res.norm_eq_ok (getMany_rename fun x hx => (hT x (hops x hx)).1) hvs)
  · obtain ⟨j, hj, hid⟩ := MidVal.WfM.block?_index hF.wf hb2
    have hidx : D.index bc.block = some j := by rw [← hid]; exact hF.wf.ids j b2 hj
    rw [hterm] at hedge
    obtain ⟨hlen, hpos⟩ := hF.edge bi b hbi _ hedge j b2 hidx hj
    have hn : n < bc.args.length := by
      have := (List.getElem?_eq_some_iff.1 hp).1
      simp only [List.length_map] at hlen; omega
    have hx0 : bc.args[n]? = some bc.args[n] := List.getElem?_eq_getElem hn
    obtain ⟨x, hx, hσ⟩ := hpos n p (some bc.args[n]) hp (by simp [hx0]) hc
    cases hx
    rw [← hσ, (hT _ (hops _ (List.mem_of_getElem? hx0))).1]
    exact (getMany_ok hvs).2 n _ hx0

/-- The terminators step in lock-step. -/
theorem CRel.termStepM {fr fr' : Frame} {bi k : Nat} {mm : Mem} (h : CRel m f D syms fr fr' bi k)
    (hs : fr.body = []) :
    (∀ fr1 m1, lstep fr mm = .next fr1 m1 → ∃ fr1', lstep fr' mm = .next fr1' m1 ∧
      CR m f D syms fr1 fr1') ∧
    (∀ vals, lstep fr mm = .ret vals → lstep fr' mm = .ret vals) ∧
    (∀ ext vals, lstep fr mm = .tail ext vals → lstep fr' mm = .tail ext vals) ∧
    (∀ c, lstep fr mm = .trap c → lstep fr' mm = .trap c) := by
  have ht : fr'.body = [] := by rw [h.body, hs]; rfl
  have hT := h.termOpsM hF hs
  have hget : ∀ x ∈ termOperands fr.term, ∀ a, fr.get x = .ok a → fr'.get (rename m x) = .ok a := by
    intro x hx a ha
    simp only [Frame.get, (hT x hx).1] at ha ⊢
    simpa [Res.ofOption_eq_ok] using ha
  have henter := fun {bc} hsucc hedge hops {fr1} (he : enterBlock fr bc = .ok fr1) =>
    enterAtM hF h.inv hs h.func h.slots h.agree (bc' := filterBC (keepMap m f)
      (mapBlockCall (rename m) bc)) hsucc he rfl (h.plainArgsM hF hs hedge hops)
  rw [lstep_term hs, lstep_term ht, h.term]
  cases hT' : fr.term with
  | jump d =>
    rw [hT'] at hget henter
    simp only [mapTerm, filterTerm]
    refine ⟨fun fr1 m1 hl => ?_, fun _ hl => ?_, fun _ _ hl => ?_, fun c hl => ?_⟩ <;>
      cases he : enterBlock fr d <;> rw [he] at hl <;> simp only [LRes.ofRes] at hl <;>
      (try cases hl)
    · obtain ⟨fr1', he', hr⟩ := henter (by simp [termSuccs]) (by simp [edges])
        (fun x hx => by simpa [termOperands] using hx) he
      exact ⟨fr1', by rw [he']; rfl, hr⟩
    · exact absurd he (enterBlock_not_trap _ _ _)
  | brif c t e =>
    rw [hT'] at hget henter
    simp only [mapTerm, filterTerm]
    have hsel : ∀ cv : Val, (if Sem.truthy cv.bits then filterBC (keepMap m f) (mapBlockCall (rename m) t)
        else filterBC (keepMap m f) (mapBlockCall (rename m) e)) =
        filterBC (keepMap m f) (mapBlockCall (rename m) (if Sem.truthy cv.bits then t else e)) := by
      intro cv; split <;> rfl
    have hgt : ∀ c', fr.get c ≠ .trap c' := fun c' => by simp [Frame.get_ne_trap]
    refine ⟨fun fr1 m1 hl => ?_, fun _ hl => ?_, fun _ _ hl => ?_, fun c' hl => ?_⟩
    all_goals cases hc : fr.get c with
      | trap c'' => exact absurd hc (hgt c'')
      | stuck _ => rw [hc] at hl; cases hl
      | ok cv =>
        rw [hc] at hl; simp only [LRes.ofRes] at hl
        cases he : enterBlock fr (if Sem.truthy cv.bits then t else e) with
        | trap c'' => exact absurd he (enterBlock_not_trap _ _ _)
        | stuck _ => rw [he] at hl; cases hl
        | ok fr1x =>
          rw [he] at hl; simp only [LRes.ofRes] at hl
          first
          | (cases hl; done)
          | (simp only [LRes.next.injEq] at hl
             obtain ⟨rfl, rfl⟩ := hl
             rw [hget c (by simp [termOperands]) cv hc]; simp only [LRes.ofRes]
             obtain ⟨fr1', he', hr⟩ := henter (by split <;> simp [termSuccs])
               (by split <;> simp [edges])
               (fun x hx => by
                 simp only [termOperands, List.mem_cons, List.mem_append]
                 split at hx <;> simp [hx]) he
             rw [hsel, he']
             exact ⟨fr1', rfl, hr⟩)
  | brTable x d tbl =>
    rw [hT'] at hget henter
    simp only [mapTerm, filterTerm]
    have hgt : ∀ c', fr.get x ≠ .trap c' := fun c' => by simp [Frame.get_ne_trap]
    refine ⟨fun fr1 m1 hl => ?_, fun _ hl => ?_, fun _ _ hl => ?_, fun c' hl => ?_⟩
    all_goals cases hc : fr.get x with
      | trap c'' => exact absurd hc (hgt c'')
      | stuck _ => rw [hc] at hl; cases hl
      | ok xv =>
        rw [hc] at hl; simp only [LRes.ofRes] at hl
        cases he : enterBlock fr (tbl[xv.toNat]?.getD d) with
        | trap c'' => exact absurd he (enterBlock_not_trap _ _ _)
        | stuck _ => rw [he] at hl; cases hl
        | ok fr1x =>
          rw [he] at hl; simp only [LRes.ofRes] at hl
          first
          | (cases hl; done)
          | (simp only [LRes.next.injEq] at hl
             obtain ⟨rfl, rfl⟩ := hl
             rw [hget x (by simp [termOperands]) xv hc]; simp only [LRes.ofRes]
             have hsel : ((tbl.map (mapBlockCall (rename m))).map (filterBC (keepMap m f)))[xv.toNat]?.getD
                 (filterBC (keepMap m f) (mapBlockCall (rename m) d)) =
                 filterBC (keepMap m f) (mapBlockCall (rename m) (tbl[xv.toNat]?.getD d)) := by
               rw [List.getElem?_map, List.getElem?_map]; cases tbl[xv.toNat]? <;> rfl
             have hmem : tbl[xv.toNat]?.getD d = d ∨ tbl[xv.toNat]?.getD d ∈ tbl := by
               cases hq : tbl[xv.toNat]? with
               | none => exact .inl rfl
               | some q => exact .inr (List.mem_of_getElem? hq)
             obtain ⟨fr1', he', hr⟩ := henter (by
                 simp only [termSuccs, List.mem_cons, List.mem_map]
                 rcases hmem with hm | hm
                 · exact .inl (by rw [hm])
                 · exact .inr ⟨_, hm, rfl⟩)
               (by
                 simp only [edges, List.mem_cons, List.mem_map]
                 rcases hmem with hm | hm
                 · exact .inl (by rw [hm])
                 · exact .inr ⟨_, hm, rfl⟩)
               (fun y hy => by
                 simp only [termOperands, List.mem_cons, List.mem_append, List.mem_flatMap]
                 rcases hmem with hm | hm
                 · rw [hm] at hy; exact .inl (.inr hy)
                 · exact .inr ⟨_, hm, hy⟩) he
             rw [hsel, he']
             exact ⟨fr1', rfl, hr⟩)
  | ret xs =>
    simp only [mapTerm, filterTerm]
    have hg := getMany_rename (fr := fr) (fr' := fr') (σ := rename m) (xs := xs)
      (fun x hx => (hT x (by rw [hT']; exact hx)).1)
    refine ⟨fun fr1 m1 hl => ?_, fun vals hl => ?_, fun _ _ hl => ?_, fun c' hl => ?_⟩
    all_goals cases hc : fr.getMany xs with
      | trap c'' => exact absurd hc (getMany_not_trap _ _ _)
      | stuck _ => rw [hc] at hl; cases hl
      | ok vs =>
        rw [hc] at hl; simp only [LRes.ofRes] at hl
        first
        | (cases hl; done)
        | (simp only [LRes.ret.injEq] at hl; subst hl; rw [Res.norm_eq_ok hg hc]; rfl)
  | returnCall fn args =>
    simp only [mapTerm, filterTerm]
    have hg := tailArgs_rename (fr := fr) (fr' := fr') (σ := rename m) (fn := fn) (args := args)
      h.externs h.sig (fun x hx => (hT x (by rw [hT']; exact hx)).1)
    refine ⟨fun fr1 m1 hl => ?_, fun vals hl => ?_, fun _ _ hl => ?_, fun c' hl => ?_⟩
    all_goals cases hc : tailArgs fr fn args with
      | trap c'' =>
        rw [hc] at hl
        first
        | (cases hl; done)
        | (cases hl; rw [Res.norm_eq_trap hg hc]; rfl)
      | stuck _ => rw [hc] at hl; cases hl
      | ok p =>
        obtain ⟨e, vs⟩ := p
        rw [hc] at hl; simp only [LRes.ofRes] at hl
        first
        | (cases hl; done)
        | (simp only [LRes.tail.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl
           rw [Res.norm_eq_ok hg hc]; rfl)
  | tryCall _ _ _ =>
    refine ⟨fun _ _ hl => ?_, fun _ hl => ?_, fun _ _ hl => ?_, fun _ hl => ?_⟩ <;> cases hl
  | tryCallIndirect _ _ _ =>
    refine ⟨fun _ _ hl => ?_, fun _ hl => ?_, fun _ _ hl => ?_, fun _ hl => ?_⟩ <;> cases hl
  | trap c =>
    simp only [mapTerm, filterTerm]
    exact ⟨(fun _ _ hl => by cases hl), (fun _ hl => by cases hl), (fun _ _ hl => by cases hl),
      (fun _ hl => hl)⟩

end

section
variable {m : Std.HashMap ValueId ValueId} {f : Function} {D : WfData} (hF : CpFactsM m f D)
  {syms : String → Option Nat}
include hF

/-- After a `try_call` returns: the results are bound at each side's fresh value and both frames
enter the normal-return successor, the target with the kept arguments. -/
theorem CRel.tcontM {fr fr' : Frame} {bi k : Nat} (h : CRel m f D syms fr fr' bi k)
    (hs : fr.body = []) (hw : Win fr fr') {et : ExnTable} {n : Nat} {bc bc' : BlockCall}
    {rtys : List Ty} (hedge : (et.normal.block, et.normal.args.map argVal) ∈ edges fr.term)
    (hsucc : et.normal.block ∈ termSuccs fr.term)
    (hvals : ∀ x ∈ et.normal.vals, x ∈ termOperands fr.term)
    (hbc : tryNormal et fr.func.freshValue = .ok bc)
    (hbc' : tryNormal (filterEt (keepMap m f) (et.mapVals (rename m))) fr'.func.freshValue = .ok bc') :
    TCont (CR m f D syms) fr (tryRets n fr.func.freshValue) bc fr' (tryRets n fr'.func.freshValue)
      bc' rtys := by
  have hf := h.inv.func
  have hg := h.func
  have hT := h.termOpsM hF hs
  have hbc0 := hbc
  rw [tryNormal_eq] at hbc0
  simp only [Res.bind_eq_ok, Res.pure_eq_ok] at hbc0
  obtain ⟨bargs, hres, rfl⟩ := hbc0
  intro vs regs _ hset
  obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs) (xs := tryRets n fr'.func.freshValue)
    (vs := vs) (by have := (setMany_spec hset).1; simp only [tryRets, List.length_map,
      List.length_range] at this ⊢; exact this)
  refine ⟨regs', hset', fun fr1 he1 => ?_⟩
  have hlo : ∀ v < f.freshValue, regs v = fr.regs v := by
    intro v hv
    refine ((setMany_spec hset).2 v).1 fun hm => ?_
    obtain ⟨j, -, he⟩ := List.mem_map.1 hm
    have he' : fr.func.freshValue + j = v := he
    rw [hf] at he'
    exact no_window' he' hv
  have hlo' : ∀ v < (cpFun m f).freshValue, regs' v = fr'.regs v := by
    intro v hv
    refine ((setMany_spec hset').2 v).1 fun hm => ?_
    obtain ⟨j, -, he⟩ := List.mem_map.1 hm
    have he' : fr'.func.freshValue + j = v := he
    rw [hg] at he'
    exact no_window' he' hv
  have hinvA : Inv f D syms { fr with regs } bi k := MidVal.WfM.inv_regs_congr hF.wf h.inv hlo
  have hagreeA : ∀ v, Avail D bi k v →
      ({ fr' with regs := regs' } : Frame).regs (rename m v) = ({ fr with regs } : Frame).regs v := by
    intro v hv
    show regs' _ = regs _
    rw [hlo' _ (rename_ltM hF hv), hlo _ (MidVal.WfM.avail_lt hF.wf hv)]
    exact h.agree v hv
  obtain ⟨bc2, hbc2, hblk, hpw⟩ := tryNormal_pair (rename m) (et := et)
    (et' := et.mapVals (rename m)) rfl (b2 := fr'.func.freshValue) hbc
  have hf2 := tryNormal_filter (keepMap m f) hbc2
  rw [hbc'] at hf2
  cases hf2
  refine enterAtM (fr' := { fr' with regs := regs' }) hF hinvA hs hg h.slots hagreeA hsucc he1
    (by simpa using hblk) ?_
  intro vs1 hga
  refine ⟨?_, fun b2 hb2 i p hp hc => ?_⟩
  · have hga' : Frame.getMany { fr' with regs := regs' } bc2.args = .ok vs1 := by
      refine getMany_pw2 (A := { fr with regs }) (hpw.imp fun x y hxy => ?_) hga
      simp only
      rcases hxy with ⟨v, hv, hx, hy⟩ | ⟨i, hx, hy⟩
      · rw [hx, hy]
        obtain ⟨h1, h2, h3⟩ := hT v (hvals v hv)
        rw [hlo' _ h3, hlo _ h2, h1]
      · rw [hx, hy, setMany_tryRets hset i, setMany_tryRets hset' i]
        split
        · rfl
        · exact (hw i).symm
    rw [hblk]
    exact getMany_filt _ _ hga'
  · obtain ⟨j, hj, hid⟩ := MidVal.WfM.block?_index hF.wf hb2
    have hid' : b2.id = et.normal.block := hid
    have hidx : D.index et.normal.block = some j := by rw [← hid']; exact hF.wf.ids j b2 hj
    obtain ⟨bb, hbi, -, hterm⟩ := inv_atEnd h.inv hs
    rw [hterm] at hedge
    obtain ⟨hlen, hpos⟩ := hF.edge bi bb hbi _ hedge j b2 hidx hj
    have hn : i < et.normal.args.length := by
      have := (List.getElem?_eq_some_iff.1 hp).1
      simp only [List.length_map] at hlen; omega
    have hx0 : et.normal.args[i]? = some et.normal.args[i] := List.getElem?_eq_getElem hn
    obtain ⟨x, hx, hσ⟩ := hpos i p (argVal et.normal.args[i]) hp (by simp [hx0]) hc
    have hval : et.normal.args[i] = .val x := by
      cases ha : et.normal.args[i] with
      | val v => rw [ha] at hx; simp only [argVal, Option.some.injEq] at hx; rw [hx]
      | ret _ => rw [ha] at hx; simp [argVal] at hx
      | exn _ => rw [ha] at hx; simp [argVal] at hx
    have hbargs : bargs[i]? = some x := resolve_val _ _ hres i x (by rw [hx0, hval])
    have hxv : x ∈ et.normal.vals := by
      simp only [TryDest.vals]
      exact List.mem_filterMap.2 ⟨.val x, by rw [← hval]; exact List.getElem_mem hn, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hT x (hvals x hxv)
    show regs' (rename m p.1) = vs1[i]?
    rw [← hσ, hlo' _ h3, h1, ← hlo _ h2]
    exact (getMany_ok hga).2 i x hbargs



/-- After a `try_call`'s callee unwinds: the tables catch alike and the frames resumed at a
handler enter related blocks, the target with the kept arguments. -/
theorem CRel.hcontM {fr fr' : Frame} {bi k : Nat} (h : CRel m f D syms fr fr' bi k)
    (hs : fr.body = []) (hw : Win fr fr') {et : ExnTable}
    (hedge : ∀ d ∈ et.handlers, (d.block, d.args.map argVal) ∈ edges fr.term)
    (hsucc : ∀ d ∈ et.handlers, d.block ∈ termSuccs fr.term)
    (hvals : ∀ d ∈ et.handlers, ∀ x ∈ d.vals, x ∈ termOperands fr.term) :
    HCont (CR m f D syms) fr et fr' (filterEt (keepMap m f) (et.mapVals (rename m))) := by
  have hf := h.inv.func
  have hg := h.func
  have hT := h.termOpsM hF hs
  intro e
  refine ⟨fun hn => ?_, fun fr1 hc => ?_⟩
  · rw [catchIn_eq_none] at hn ⊢
    rw [catch?_filterEt, catch?_mapVals, hn]; rfl
  · obtain ⟨d, bc, regs, hd, hbc, hset, rfl⟩ := catchIn_ok hc
    have hdm := catch?_mem hd
    have hbc0 := hbc
    rw [tryHandler_eq] at hbc0
    simp only [Res.bind_eq_ok, Res.pure_eq_ok] at hbc0
    obtain ⟨bargs, hres, rfl⟩ := hbc0
    obtain ⟨bc2, hbc2, hblk, hpw⟩ := tryHandler_pair (rename m) (b2 := fr'.func.freshValue) hbc
    have hbc' := tryHandler_filter (keepMap m f) hbc2
    obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs)
      (xs := (List.range e.payload.length).map (fr'.func.freshValue + ·)) (vs := e.payload)
      (by simp)
    have hd' : (filterEt (keepMap m f) (et.mapVals (rename m))).catch? e =
        some (filterTD (keepMap m f) (d.mapVals (rename m))) := by
      rw [catch?_filterEt, catch?_mapVals, hd]; rfl
    refine ⟨_, catchIn_of hd' hbc' hset', rfl, rfl, _, _, rfl, rfl, fun fr1 he1 => ?_⟩
    have he1' : enterBlock { fr with regs } ⟨d.block, bargs⟩ = .ok fr1 := by
      rw [← enterBlock_bt { fr with regs } [] (.jump ⟨d.block, bargs⟩)]; exact he1
    have hW := setMany_tryRets (n := e.payload.length) (W := fr.func.freshValue) hset
    have hW' := setMany_tryRets (n := e.payload.length) (W := fr'.func.freshValue) hset'
    have hlo : ∀ v < f.freshValue, regs v = fr.regs v := catch_regs_lo hset (by rw [hf])
    have hlo' : ∀ v < (cpFun m f).freshValue, regs' v = fr'.regs v := catch_regs_lo hset' (by rw [hg])
    have hinvA : Inv f D syms { fr with regs } bi k := MidVal.WfM.inv_regs_congr hF.wf h.inv hlo
    have hagreeA : ∀ v, Avail D bi k v →
        ({ fr' with regs := regs' } : Frame).regs (rename m v) = ({ fr with regs } : Frame).regs v := by
      intro v hv
      show regs' _ = regs _
      rw [hlo' _ (rename_ltM hF hv), hlo _ (MidVal.WfM.avail_lt hF.wf hv)]
      exact h.agree v hv
    obtain ⟨fr1', he1'', hr1⟩ := enterAtM (fr' := { fr' with regs := regs' })
      (bc' := { block := bc2.block, args := filt (keepOf (keepMap m f) bc2.block) bc2.args })
      hF hinvA hs hg h.slots hagreeA (hsucc d hdm) he1' (by simpa using hblk) (by
        intro vs1 hga
        refine ⟨?_, fun b2 hb2 i p hp hc => ?_⟩
        · have hga' : Frame.getMany { fr' with regs := regs' } bc2.args = .ok vs1 := by
            refine getMany_pw2 (A := { fr with regs }) (hpw.imp fun x y hxy => ?_) hga
            simp only
            rcases hxy with ⟨v, hv, hx, hy⟩ | ⟨i, hx, hy⟩
            · rw [hx, hy]
              obtain ⟨h1, h2, h3⟩ := hT v (hvals d hdm v hv)
              rw [hlo' _ h3, hlo _ h2, h1]
            · rw [hx, hy, hW i, hW' i]
              split
              · rfl
              · exact (hw i).symm
          rw [hblk]
          exact getMany_filt _ _ hga'
        · obtain ⟨j, hj, hid⟩ := MidVal.WfM.block?_index hF.wf hb2
          have hid' : b2.id = d.block := hid
          have hidx : D.index d.block = some j := by rw [← hid']; exact hF.wf.ids j b2 hj
          obtain ⟨bb, hbi, -, hterm⟩ := inv_atEnd h.inv hs
          have hedge' := hedge d hdm
          rw [hterm] at hedge'
          obtain ⟨hlen, hpos⟩ := hF.edge bi bb hbi _ hedge' j b2 hidx hj
          have hn : i < d.args.length := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp only [List.length_map] at hlen; omega
          have hx0 : d.args[i]? = some d.args[i] := List.getElem?_eq_getElem hn
          obtain ⟨x, hx, hσ⟩ := hpos i p (argVal d.args[i]) hp (by simp [hx0]) hc
          have hval : d.args[i] = .val x := by
            cases ha : d.args[i] with
            | val v => rw [ha] at hx; simp only [argVal, Option.some.injEq] at hx; rw [hx]
            | ret _ => rw [ha] at hx; simp [argVal] at hx
            | exn _ => rw [ha] at hx; simp [argVal] at hx
          have hbargs : bargs[i]? = some x := resolveH_val _ _ hres i x (by rw [hx0, hval])
          have hxv : x ∈ d.vals := by
            simp only [TryDest.vals]
            exact List.mem_filterMap.2 ⟨.val x, by rw [← hval]; exact List.getElem_mem hn, rfl⟩
          obtain ⟨h1, h2, h3⟩ := hT x (hvals d hdm x hxv)
          show regs' (rename m p.1) = vs1[i]?
          rw [← hσ, hlo' _ h3, h1, ← hlo _ h2]
          exact (getMany_ok hga).2 i x hbargs)
    exact ⟨fr1', (enterBlock_bt { fr' with regs := regs' } [] (.jump _) _).trans he1'', hr1⟩


/-- A `call_indirect`: the same signature, the renamed callee and arguments read the same
values; the continuations are related (result types from the signature declarations, `WfM`). -/
theorem CRel.ciM {fr fr' : Frame} {bi k : Nat} {st : Stmt} {rest : List Stmt} {sig : Nat}
    {callee : ValueId} {args : List ValueId} {d : Signature} {a : Nat} {vals : List Val}
    (h : CRel m f D syms fr fr' bi k) (hb : fr.body = st :: rest)
    (hi : st.inst = .callIndirect sig callee args)
    (hca : ciArgs fr sig callee args = .ok (d, a, vals)) :
    fr'.body = renStmt (rename m) st :: rest.map (renStmt (rename m)) ∧
      (renStmt (rename m) st).inst = .callIndirect sig (rename m callee) (args.map (rename m)) ∧
      ciArgs fr' sig (rename m callee) (args.map (rename m)) = .ok (d, a, vals) ∧
      Cont (CR m f D syms) { fr with body := rest } st.results
        { fr' with body := rest.map (renStmt (rename m)) } (renStmt (rename m) st).results
        (AbiParam.tys d.returns) := by
  obtain ⟨b, hbi, hbody, -, -⟩ := h.inv.block
  have hs := hb
  rw [hbody] at hs
  obtain ⟨hsk, -, -⟩ := drop_eq_cons hs
  have ht : fr'.body = renStmt (rename m) st :: rest.map (renStmt (rename m)) := by
    rw [h.body, hb]; rfl
  have hops : ∀ x ∈ operands st.inst, fr'.regs (rename m x) = fr.regs x :=
    fun x hx => h.agree x (hF.wf.uses bi b hbi k st hsk x hx)
  have hci : (renStmt (rename m) st).inst =
      .callIndirect sig (rename m callee) (args.map (rename m)) := by
    simp [renStmt, hi, mapOperands]
  have hca' := ciArgs_rename (σ := rename m) h.sigDecls
    (fun x hx => hops x (by rw [hi]; simpa [operands] using hx)) hca
  refine ⟨ht, hci, hca', ?_⟩
  show Cont _ _ st.results _ st.results _
  intro vs regs hty hset
  obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs) (xs := st.results) (vs := vs)
    (setMany_spec hset).1
  refine ⟨regs', hset', bi, k + 1, ?_, h.func, rfl, h.term, h.slots, ?_⟩
  · have hd : MidVal.sigDeclOf f sig = some d := by
      obtain ⟨-, -, hd, -⟩ := ciArgs_ok.1 hca
      rw [h.inv.func] at hd
      exact hd
    refine MidVal.WfM.inv_results (fr := fr) (st := st) (rest := rest) hF.wf h.inv hb
      (fun ts0 h0 => ?_) (fun hp => by rw [hi] at hp; cases hp) hset
    rw [hi, Inst.resultTypes, hd] at h0
    simp only [Option.map_some, Option.some.injEq] at h0
    rw [← h0, hty]; rfl
  · intro v hv
    rcases MidVal.WfM.avail_succ hF.wf hbi hsk hv with hr | hv'
    · rw [rename_resultM hF hbi hsk hr]
      exact (setMany_same hset hset' v hr).symm
    · show regs' (rename m v) = regs v
      rw [((setMany_spec hset').2 _).1 (rename_not_resultM hF hbi hsk hv'),
        ((setMany_spec hset).2 _).1 (MidVal.WfM.avail_not_result hF.wf hbi hsk hv'), h.agree v hv']

/-- **The frame relation is a simulation with windows and handler edges** (`CR.isSimWU` for
`CpFactsM`, with the `call_indirect` step `CRel.ciM`). -/
theorem CR.isSimWUM : IsSimWU syms (CR m f D syms) where
  toIsSim := {
    frame := by
      rintro fr fr' ⟨bi, k, h⟩
      exact ⟨h.slots, h.sig⟩
    next := by
      rintro fr fr' mm fr1 m1 ⟨bi, k, h⟩ hm hl
      cases hs : fr.body with
      | nil =>
        obtain ⟨fr1', hl', hr⟩ := (h.termStepM hF (mm := mm) hs).1 fr1 m1 hl
        exact ⟨fr1', .single hl', hr⟩
      | cons s ss =>
        have hnc : ∀ fn args, s.inst ≠ .call fn args :=
          fun fn args hc => (lstep_call_of_call hs hc).1 fr1 m1 hl
        obtain ⟨fr1', hl', hr⟩ := (h.stmtM hF hm hs hnc).1 fr1 m1 hl
        exact ⟨fr1', .single hl', bi, k + 1, hr⟩
    call := by
      rintro fr fr' mm ext vals rs rest ⟨bi, k, h⟩ hm hl
      obtain ⟨hl', hk⟩ := h.callM hF hl
      exact ⟨fr', rs, _, .refl _ _, hl', hk⟩
    ret := by
      rintro fr fr' mm vals ⟨bi, k, h⟩ hm hl
      exact ⟨fr', .refl _ _, (h.termStepM hF (mm := mm) (lstep_ret_inv hl)).2.1 vals hl⟩
    tail := by
      rintro fr fr' mm ext vals ⟨bi, k, h⟩ hm hl
      exact ⟨fr', .refl _ _, (h.termStepM hF (mm := mm) (lstep_tail_inv hl)).2.2.1 ext vals hl⟩
    trap := by
      rintro fr fr' mm c ⟨bi, k, h⟩ hm hl
      cases hs : fr.body with
      | nil => exact ⟨fr', mm, .refl _ _, (h.termStepM hF (mm := mm) hs).2.2.2 c hl⟩
      | cons s ss =>
        have hnc : ∀ fn args, s.inst ≠ .call fn args :=
          fun fn args hc => (lstep_call_of_call hs hc).2 c hl
        exact ⟨fr', mm, .refl _ _, (h.stmtM hF hm hs hnc).2 c hl⟩ }
  ci := by
    rintro fr fr' mm st rest sig callee args d a vals ⟨bi, k, h⟩ - - - - hb hi hca
    obtain ⟨ht, hci, hca', hc⟩ := h.ciM hF hb hi hca
    exact ⟨fr', _, _, _, _, _, .refl _ _, ht, hci, hca', hc⟩
  tc := by
    refine ⟨?_, ?_⟩
    · rintro fr fr' mm fn args et n base bc ext vals ⟨bi, k, h⟩ - - hw hm hb ht htc hca
      have ht' : fr'.body = [] := by rw [h.body, hb]; rfl
      have hterm' : fr'.term = .tryCall fn (args.map (rename m))
          (filterEt (keepMap m f) (et.mapVals (rename m))) := by
        rw [h.term, ht]; rfl
      have hT := h.termOpsM hF hb
      rw [ht] at hT
      obtain ⟨e0, s0, he0, hs0, hc0, rfl, hbc, rfl⟩ := tcArgs_ok.1 htc
      obtain ⟨bc2, hbc2, -, -⟩ := tryNormal_pair (rename m) (et := et)
        (et' := et.mapVals (rename m)) rfl (b2 := fr'.func.freshValue) hbc
      have hbc' := tryNormal_filter (keepMap m f) hbc2
      have htc' : tcArgs fr' fn (filterEt (keepMap m f) (et.mapVals (rename m))) =
          .ok (e0.sig.returns.length, fr'.func.freshValue,
            { block := bc2.block, args := filt (keepOf (keepMap m f) bc2.block) bc2.args }) := by
        refine tcArgs_ok.2 ⟨e0, s0, ?_, ?_, hc0, rfl, hbc', rfl⟩
        · rw [← he0]; simp only [Function.extern?, h.externs]
        · rw [← hs0, h.sigDecls]; rfl
      have hca' : callArgs fr' fn (args.map (rename m)) = .ok (ext, vals) :=
        Res.norm_eq_ok (callArgs_rename h.externs
          (fun x hx => (hT x (by simp [termOperands, hx])).1)) hca
      refine ⟨fr', fn, args.map (rename m), _, _, _, .refl _ _, ht', hterm', htc', hca', ?_, ?_⟩
      · exact h.tcontM hF hb hw (by rw [ht]; exact List.mem_map.2 ⟨et.normal, dests_normal et, rfl⟩)
          (by rw [ht]; exact List.mem_map.2 ⟨et.normal, dests_normal et, rfl⟩)
          (fun x hx => by rw [ht]; exact normal_vals_sub x hx) hbc hbc'
      · exact h.hcontM hF hb hw (fun d hd => by rw [ht]; exact handlers_edge hd)
          (fun d hd => by rw [ht]; exact handler_succ hd)
          (fun d hd x hx => by rw [ht]; simp [termOperands, handler_vals hd hx])
    · rintro fr fr' mm callee args et n base bc d a vals ⟨bi, k, h⟩ - - hw hm hb ht htc hca
      have ht' : fr'.body = [] := by rw [h.body, hb]; rfl
      have hterm' : fr'.term = .tryCallIndirect (rename m callee) (args.map (rename m))
          (filterEt (keepMap m f) (et.mapVals (rename m))) := by
        rw [h.term, ht]; rfl
      have hT := h.termOpsM hF hb
      rw [ht] at hT
      obtain ⟨s0, hs0, rfl, hbc, rfl⟩ := ticArgs_ok.1 htc
      obtain ⟨bc2, hbc2, -, -⟩ := tryNormal_pair (rename m) (et := et)
        (et' := et.mapVals (rename m)) rfl (b2 := fr'.func.freshValue) hbc
      have hbc' := tryNormal_filter (keepMap m f) hbc2
      have htc' : ticArgs fr' (filterEt (keepMap m f) (et.mapVals (rename m))) =
          .ok (s0.returns.length, fr'.func.freshValue,
            { block := bc2.block, args := filt (keepOf (keepMap m f) bc2.block) bc2.args }) :=
        ticArgs_ok.2 ⟨s0, by rw [← hs0, h.sigDecls]; rfl, rfl, hbc', rfl⟩
      have hca' : ciArgs fr' (filterEt (keepMap m f) (et.mapVals (rename m))).sig (rename m callee)
          (args.map (rename m)) = .ok (d, a, vals) :=
        ciArgs_rename h.sigDecls
          (fun x hx => (hT x (by
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · simp [termOperands]
            · simp [termOperands, hx])).1) hca
      refine ⟨fr', rename m callee, args.map (rename m), _, _, _, .refl _ _, ht', hterm', htc', hca',
        ?_, ?_⟩
      · exact h.tcontM hF hb hw (by rw [ht]; exact List.mem_map.2 ⟨et.normal, dests_normal et, rfl⟩)
          (by rw [ht]; exact List.mem_map.2 ⟨et.normal, dests_normal et, rfl⟩)
          (fun x hx => by rw [ht]; exact normal_vals_sub' x hx) hbc hbc'
      · exact h.hcontM hF hb hw (fun d hd => by rw [ht]; exact handlers_edge hd)
          (fun d hd => by rw [ht]; exact handler_succ hd)
          (fun d hd x hx => by rw [ht]; simp [termOperands, handler_vals hd hx])

end

end Opt.ConstPhi

namespace Opt.MidVal

open Clif Opt ConstPhi

/-- `phiOkM` gives the facts `CpFactsM` (the proof of `phiOk_facts`, with `wfM_of_wfCheck`). -/
theorem phiOkM_facts {f : Function} {sol : List (ValueId × ValueId)} (h : phiOkM f sol = true) :
    ∃ fi, wfCheck f = .ok fi ∧ CpFactsM (solMap sol) f (wfData f fi) := by
  unfold phiOkM at h
  split at h
  · cases h
  rename_i fi hfi
  simp only [Bool.and_eq_true] at h
  obtain ⟨hkeys, hedges⟩ := h
  refine ⟨fi, hfi, wfM_of_wfCheck hfi, fun x hx => ?_, fun i b hb e he j db hj hdb => ?_⟩
  · have hmem := solMap_get (get_of_contains hx)
    simp only [keysOk, Bool.and_eq_true, List.all_eq_true] at hkeys
    have h1 := hkeys.2 _ hmem
    simp only [Bool.not_eq_true'] at h1
    obtain ⟨hnc, h2⟩ := h1
    split at h2
    · rename_i bp dv t hp hv
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h2
      obtain ⟨⟨hbp, hdv⟩, ha⟩ := h2
      exact ⟨bp, dv, t, by simpa [wfData, Std.HashMap.get?_eq_getElem?] using hp, hbp, hnc,
        by simpa [wfData, Std.HashMap.get?_eq_getElem?] using hv, hdv, ancB_sound ha⟩
    · cases h2
  · simp only [edgesOk, List.all_eq_true] at hedges
    have h1 := hedges b (List.mem_of_getElem? hb) e he
    have hj' : fi.cfg.index[e.1]? = some j := by
      simpa [wfData, Std.HashMap.get?_eq_getElem?] using hj
    obtain ⟨dst, args⟩ := e
    simp only at h1 hj' ⊢
    simp only [hj', hdb, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h1
    obtain ⟨hlen, hall⟩ := h1
    refine ⟨hlen, fun n p a hp ha hc => ?_⟩
    have hz : (p, a) ∈ db.params.zip args :=
      List.mem_iff_getElem?.2 ⟨n, by simp [List.getElem?_zip_eq_some, hp, ha]⟩
    have h2 := hall _ hz
    simp only [hc, Bool.not_true, Bool.false_or] at h2
    split at h2
    · rename_i x
      exact ⟨x, rfl, by simpa using h2⟩
    · cases h2

/-- **An accepted solution's rewrite is simulated by its input, `call_indirect` included**
(`phiOk_simU`'s proof from `phiOkM_facts` and `CR.isSimWUM`). -/
theorem phiOkM_simU {f : Function} {sol : List (ValueId × ValueId)} (h : phiOkM f sol = true) :
    FunSimU f (apply f sol) := by
  obtain ⟨fi, -, hF⟩ := phiOkM_facts h
  rw [ConstPhi.apply_eq]
  refine FunSimU.ofWU rfl rfl rfl rfl fun syms =>
    ⟨_, ConstPhi.CR.isSimWUM hF (syms := syms), fun b hb => ?_⟩
  have hb0 : f.blocks[0]? = some b := by
    simpa [Function.entry?, List.head?_eq_getElem?] using hb
  have hkeep : ∀ p ∈ b.params, (solMap sol).contains p.1 = false := by
    intro p hp
    cases hc : (solMap sol).contains p.1
    · rfl
    · obtain ⟨bp, -, -, hd, hbp, -⟩ := hF.key p.1 hc
      rw [WfM.site_param hF.wf hb0 hp] at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      exact absurd hd.1.symm hbp
  have hpar : (cpBlock (solMap sol) (keepMap (solMap sol) f) b).params = b.params := by
    simp only [cpBlock]
    exact List.filter_eq_self.2 (fun p hp => by simp [hkeep p hp])
  refine ⟨cpBlock _ _ b, by rw [cpFun_entry?, hb]; rfl, hpar,
    fun args regs slots hty hr hsl => ⟨0, 0, WfM.inv_entry hF.wf hb hty hr hsl, rfl, rfl, rfl, rfl,
      fun v hv => ?_⟩⟩
  obtain ⟨b1, p, hb1, hp, hpv⟩ := WfM.site_param' hF.wf (WfM.avail_entry hF.wf hv)
  rw [hb0] at hb1; cases hb1
  show regs (ConstPhi.rename (solMap sol) v) = regs v
  rw [← hpv, rename_of_not (hkeep p hp)]

end Opt.MidVal
