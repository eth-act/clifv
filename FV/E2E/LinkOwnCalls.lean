import FV.E2E.LinkOwnCallsDefs
import FV.E2E.SpillCtlCheck

/-! # The call sites of the compiler's own output (`callRegs/blrRegs`; L2a)

`sites_of_lower`: for an in-scope function `g` of `P` whose call sites pass the input condition
`callScopeB P S g` (`LinkOwnCallsDefs`), every call site of the prepared VCode passes `siteOk`
(registers of the callee's parameters, results from x0), against every program function the
site may enter.

The lowering's call sites are stated relative to the CLIF call site's signature
(`CallShapeHyp`, program-independent): each `call`/`tryCall` of `lowerFunction`'s VCode is the
call of a CLIF call site of `f` — a direct call of an extern `e` (`bl e.name`, or `blr` of a vreg
whose GOT symbol, `gotOf`, is `e.name`) or an indirect call of a signature `s` (`blr` of an int
vreg) — whose uses are `retPairs` of its argument vregs in the registers `callRegs` of the
signature, whose defs are `callDefs` in x0, x1, …, and (a `tryCall`) whose `rets` is the
signature's number of ABI results. The transfer to the callee `h` of `P`:

* a `bl e.name` with `P.func? e.name = some h`: `g` declares it (possibly itself), and
  `callRegs e.sig args = regLocs h.sig` (`dirSiteB`); its `rets` are `h`'s
  (the declared signature `e.sig = h.sig`);
* a GOT `blr`: the GOT symbol restricts the callees to `h` named `e.name`, as for `bl`;
* an indirect `blr`: every callee the site may enter (`indSiteB`).

`prepare` keeps the call sites (a retargeted `tryCall` keeps its `CallInfo` and `rets`) and the
GOT symbols (`gotOf_prep`: it keeps every instruction defining a vreg, and a call through a vreg
keeps the GOT load before it in its block).
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill

/-! ## The lowering's call sites -/

/-- A call's operands: the uses `retPairs L` with argument registers `rs`, the defs `callDefs D`
in x0, x1, …. -/
def ShapeOf (rs : List Reg) (c : CallInfo) : Prop :=
  ∃ L D, c.uses = retPairs L ∧ c.defs = callDefs D ∧ L.map (·.2) = rs ∧
    D.map (·.1) = (List.range D.length).map Reg.x

/-- `f` has a direct call (`isTry`: a `try_call` terminator, else a `call` statement) of the
extern `e` with arguments `args`. -/
def DirSite (f : Clif.Function) (isTry : Bool) (args : List Nat) (e : Clif.ExtFunc) : Prop :=
  ∃ fn, f.extern? fn = some e ∧ ∃ B ∈ f.blocks,
    (isTry = false ∧ ∃ st ∈ B.body, st.inst = .call fn args) ∨
    (isTry = true ∧ ∃ et, B.term = .tryCall fn args et)

/-- `f` has an indirect call (`isTry`: a `try_call_indirect` terminator, else a `call_indirect`
statement) of the declared signature `s` with arguments `args`. -/
def IndSite (f : Clif.Function) (isTry : Bool) (args : List Nat) (s : Clif.Signature) : Prop :=
  ∃ B ∈ f.blocks,
    (isTry = false ∧ ∃ st ∈ B.body, ∃ sg callee, st.inst = .callIndirect sg callee args ∧
      f.sigDecls.lookup sg = some s) ∨
    (isTry = true ∧ ∃ callee et, B.term = .tryCallIndirect callee args et ∧
      f.sigDecls.lookup et.sig = some s)

/-- **The call `c` of a call site of `f`** in the VCode `vc` (`isTry`: of a `tryCall` with `rets`
results): of a direct call of `e` (`bl e.name`, or `blr` of an int vreg whose GOT symbol in
`vc` is `e.name`), or of an indirect call of signature `s` (`blr` of an int vreg); its operands
have the shape `ShapeOf` with the registers `callRegs` of the signature. -/
def SiteCall (f : Clif.Function) (vc : VCode) (isTry : Bool) (rets : Nat) (c : CallInfo) : Prop :=
  ∃ args,
    (∃ e, DirSite f isTry args e ∧ ShapeOf (callRegs e.sig args) c ∧
      (isTry = true → rets = (sigRets e.sig).length) ∧
      (c.dest = .sym e.name ∨ ∃ t, c.dest = .reg (.vreg t .int) ∧ gotOf vc t = some e.name)) ∨
    (∃ s, IndSite f isTry args s ∧ ShapeOf (callRegs s args) c ∧
      (isTry = true → rets = (sigRets s).length) ∧ ∃ t, c.dest = .reg (.vreg t .int))

/-- **The ISLE call lowering against the call site's signature** (program-independent): every
`call` of `lowerFunction`'s VCode of an in-scope function is the call of one of its `call`/
`call_indirect` statements, every `tryCall` the call of one of its `try_call`/
`try_call_indirect` terminators (`SiteCall`). -/
def CallShapeHyp : Prop :=
  ∀ (p : Clif.Program) (f : Clif.Function) (vc : VCode), InSubset p f → Dominated f →
    LowerScope f → lowerFunction f = .ok vc →
    ∀ (b : Nat) (vb : VBlock) (k : Nat), vc.blocks[b]? = some vb →
      (∀ c, vb.insts[k]? = some (.call c) → SiteCall f vc false 0 c) ∧
      (∀ c ti, vb.insts[k]? = some (.tryCall c ti) → SiteCall f vc true ti.rets c)

/-! ## `prepare` keeps the call sites -/

/-- **The source of an instruction of the prepared VCode**: the instruction at the same index of
a block of the input (possibly retargeted), the instructions before it unchanged; or an edge
block's `jump`. -/
theorem prep_src {vc vcp : VCode} (hp : prepare vc = .ok vcp) (hd : Prep.PrepDomain vc)
    {q : Nat} {vb : VBlock} {k : Nat} {i : MInst} (hvb : vcp.blocks[q]? = some vb)
    (hi : vb.insts[k]? = some i) :
    (∃ (b : Nat) (vb0 : VBlock) (i0 : MInst), vc.blocks[b]? = some vb0 ∧ vb0.insts[k]? = some i0 ∧
      (i0 = i ∨ ∃ ls, i0.setTargets ls = some i) ∧ ∀ j < k, vb.insts[j]? = vb0.insts[j]?) ∨
    ∃ l, i = .jump l := by
  obtain ⟨ss0, ps0, ss1, ps1, ss2, ps2, next, B, E, hc0, hc1, hS, hc2, rfl⟩ := Prep.prepare_facts hp
  have cs0 := Prep.cfg_spec hc0
  have cs2 : Prep.CfgSpec (B ++ E) ss2 := Prep.cfg_spec hc2
  obtain ⟨h10, hk0, -, hn1, -, hR, hRn, hR0, -, -⟩ := Prep.facts_basic hd cs0 cs2 hS
  have hqR : q < (rpo ss2).size := by
    have := (Array.getElem?_eq_some_iff.mp hvb).1; simpa using this
  obtain ⟨hj, e⟩ := Prep.v3_get hR hqR
  rw [e] at hvb
  cases hvb
  by_cases hjB : (rpo ss2)[q] < B.size
  · left
    rw [Array.getElem_append_left hjB] at hi ⊢
    have hj1 : (rpo ss2)[q] < (Prep.keep vc.blocks (reachable ss0)).size := by
      rw [← hS.size]; exact hjB
    obtain ⟨b, hb, eb, -⟩ := Prep.keep_src hj1
    rcases hS.rw _ hj1 hjB with h | ⟨t, t', ls, h1, -, h3, h4, -⟩
    · rw [h, eb] at hi ⊢
      exact ⟨b, _, i, Array.getElem?_eq_getElem hb, hi, .inl rfl, fun _ _ => rfl⟩
    · rw [h4, eb] at hi ⊢
      rw [eb, Array.back?_eq_getElem?] at h1
      refine ⟨b, vc.blocks[b], ?_⟩
      simp only [Array.getElem?_push, Array.size_pop] at hi ⊢
      split at hi
      · rename_i hk
        cases hi
        refine ⟨t, Array.getElem?_eq_getElem hb, ?_, .inr ⟨ls, h3⟩, fun j hj => ?_⟩
        · rw [hk]; exact h1
        · rw [ite_eq_right (by omega), Array.getElem?_pop, ite_eq_left (by omega)]
      · rw [Array.getElem?_pop] at hi
        split at hi
        · refine ⟨i, Array.getElem?_eq_getElem hb, hi, .inl rfl, fun j hj => ?_⟩
          rw [ite_eq_right (by omega), Array.getElem?_pop, ite_eq_left (by omega)]
        · cases hi
  · right
    have he : (rpo ss2)[q] - B.size < E.size := by simp at hj; omega
    obtain ⟨l, hl⟩ := hS.edges _ he
    rw [Array.getElem_append_right (by omega), hl] at hi
    have hm := Array.mem_of_getElem? hi
    simp at hm
    exact ⟨l, hm⟩

/-- Retargeting never gives a `call`. -/
theorem setTargets_ne_call {i : MInst} {ls : List Label} {c : CallInfo}
    (h : i.setTargets ls = some (.call c)) : False := by
  unfold MInst.setTargets at h
  split at h
  all_goals (try split at h)
  all_goals cases h

/-- Retargeting gives a `tryCall` only from a `tryCall` with the same `CallInfo` and `rets`. -/
theorem setTargets_eq_tryCall {i : MInst} {ls : List Label} {c : CallInfo} {ti : TryInfo}
    (h : i.setTargets ls = some (.tryCall c ti)) : ∃ ti0, i = .tryCall c ti0 ∧ ti0.rets = ti.rets := by
  unfold MInst.setTargets at h
  split at h
  all_goals (try split at h)
  all_goals (try cases h; done)
  cases h
  exact ⟨_, rfl, rfl⟩

theorem setTargets_got {r : Reg} {n : String} {ls : List Label} {i : MInst}
    (h : (MInst.loadExtNameGot r n).setTargets ls = some i) : False := by
  simp [MInst.setTargets] at h

/-- The source of a call site of the prepared VCode is a call site of the input, the same
`CallInfo` (and `rets`), the instructions before it unchanged. -/
theorem prep_site {vc vcp : VCode} (hp : prepare vc = .ok vcp) (hd : Prep.PrepDomain vc)
    {q : Nat} {vb : VBlock} {k : Nat} {i : MInst} (hvb : vcp.blocks[q]? = some vb)
    (hi : vb.insts[k]? = some i) :
    (∀ c, i = .call c → ∃ (b : Nat) (vb0 : VBlock), vc.blocks[b]? = some vb0 ∧
      vb0.insts[k]? = some (MInst.call c) ∧ ∀ j < k, vb.insts[j]? = vb0.insts[j]?) ∧
    (∀ c ti, i = .tryCall c ti → ∃ (b : Nat) (vb0 : VBlock) (ti0 : TryInfo),
      vc.blocks[b]? = some vb0 ∧ vb0.insts[k]? = some (MInst.tryCall c ti0) ∧ ti0.rets = ti.rets ∧
      ∀ j < k, vb.insts[j]? = vb0.insts[j]?) := by
  rcases prep_src hp hd hvb hi with ⟨b, vb0, i0, hb, hi0, hs, hpre⟩ | ⟨l, rfl⟩
  · refine ⟨fun c hc => ?_, fun c ti hc => ?_⟩
    · subst hc
      rcases hs with rfl | ⟨ls, hls⟩
      · exact ⟨b, vb0, hb, hi0, hpre⟩
      · exact (setTargets_ne_call hls).elim
    · subst hc
      rcases hs with rfl | ⟨ls, hls⟩
      · exact ⟨b, vb0, ti, hb, hi0, rfl, hpre⟩
      · obtain ⟨ti0, rfl, hr⟩ := setTargets_eq_tryCall hls
        exact ⟨b, vb0, ti0, hb, hi0, hr, hpre⟩
  · refine ⟨fun c h => ?_, fun c ti h => ?_⟩ <;> cases h

/-! ## `prepare` keeps the GOT symbols -/

theorem findSome_eq {α β : Type} {F : α → Option β} {n : β} :
    ∀ {l : List α}, (∀ x ∈ l, ∀ m, F x = some m → m = n) → (∃ x ∈ l, F x = some n) →
      l.findSome? F = some n
  | [], _, ⟨_, hx, _⟩ => by cases hx
  | a :: l, hall, ⟨x, hx, hF⟩ => by
    rw [List.findSome?_cons]
    cases ha : F a with
    | some m => rw [hall a List.mem_cons_self m ha]
    | none =>
      simp only
      refine findSome_eq (fun y hy => hall y (List.mem_cons_of_mem _ hy)) ?_
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [ha] at hF; cases hF
      · exact ⟨x, hx, hF⟩

theorem gotBefore_congr {t : Nat} {n : String} {vb vb0 : VBlock} {k : Nat}
    (h : ∀ j < k, vb.insts[j]? = vb0.insts[j]?) : gotBefore t n vb k = gotBefore t n vb0 k := by
  unfold gotBefore
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, h'⟩; exact ⟨j, hj, by rw [← h j hj]; exact h'⟩
  · rintro ⟨j, hj, h'⟩; exact ⟨j, hj, by rw [h j hj]; exact h'⟩

theorem operands_got (t : Nat) (n : String) :
    ∃ ops, (MInst.loadExtNameGot (.vreg t .int) n).operands = .ok ops ∧
      ∃ o ∈ ops.toList, o.isDef = true ∧ o.vreg = t :=
  ⟨_, rfl, _, List.mem_singleton_self _, rfl, rfl⟩

/-- **`prepare` keeps the GOT symbol** of the target of a call it keeps. -/
theorem gotOf_prep {vc vcp : VCode} (hp : prepare vc = .ok vcp) (hd : Prep.PrepDomain vc)
    {t : Nat} {n : String} (hg : gotOf vc t = some n) {q : Nat} {vb : VBlock} {k : Nat}
    {c : CallInfo} (hvb : vcp.blocks[q]? = some vb)
    (hk : vb.insts[k]? = some (.call c) ∨ ∃ ti, vb.insts[k]? = some (.tryCall c ti))
    (hdst : c.dest = .reg (.vreg t .int)) : gotOf vcp t = some n := by
  have hb : gotB vc t n = true := by
    unfold gotOf at hg
    cases hs : gotSym vc t with
    | none => simp [hs] at hg
    | some n' =>
      simp only [hs] at hg
      split at hg
      · cases hg; assumption
      · cases hg
  simp only [gotB] at hb
  have hB : ∀ b vb, vc.blocks[b]? = some vb → vb.insts.all (gotDefB t n) = true ∧
      (List.range vb.insts.size).all (gotSiteB t n vb) = true := fun b vb hvb => by
    simpa only [Bool.and_eq_true] using (array_all_iff _ _).1 hb b vb hvb
  -- every instruction of `vcp` defining `t` is the GOT load
  have hdef : ∀ (q : Nat) (vb : VBlock) (k : Nat) (i : MInst), vcp.blocks[q]? = some vb →
      vb.insts[k]? = some i → gotDefB t n i = true := by
    intro q vb k i hq hi
    rcases prep_src hp hd hq hi with ⟨b, vb0, i0, hb0, hi0, hs, -⟩ | ⟨l, rfl⟩
    · have h0 := (array_all_iff _ _).1 (hB b vb0 hb0).1 k i0 hi0
      rcases hs with rfl | ⟨ls, hls⟩
      · exact h0
      · have hops := (setTargets_facts hls).1
        unfold gotDefB at h0 ⊢
        rw [hops]
        revert h0
        split
        · intro h0
          simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h0
          rcases h0 with h0 | h0
          · simp [h0]
          · subst h0; exact (setTargets_got hls).elim
        · intro _; rfl
    · simp [gotDefB, MInst.operands, MInst.visitOperands, StateT.run, bind, pure, StateT.pure,
        Except.pure, Except.bind]
  -- every call through `t` in `vcp` follows the GOT load in its block
  have hsite : ∀ (q : Nat) (vb : VBlock), vcp.blocks[q]? = some vb →
      ∀ k, gotSiteB t n vb k = true := by
    intro q vb hq k
    unfold gotSiteB
    cases hi : vb.insts[k]? with
    | none => rfl
    | some i =>
      obtain ⟨hc, hy⟩ := prep_site hp hd hq hi
      cases i with
      | call c =>
        obtain ⟨b, vb0, hb0, hi0, hpre⟩ := hc c rfl
        have hk0 : k < vb0.insts.size := (Array.getElem?_eq_some_iff.mp hi0).1
        have := List.all_eq_true.mp (hB b vb0 hb0).2 k (List.mem_range.mpr hk0)
        simp only [gotSiteB, hi0] at this
        simp only [gotBefore_congr hpre]
        exact this
      | tryCall c ti =>
        obtain ⟨b, vb0, ti0, hb0, hi0, -, hpre⟩ := hy c ti rfl
        have hk0 : k < vb0.insts.size := (Array.getElem?_eq_some_iff.mp hi0).1
        have := List.all_eq_true.mp (hB b vb0 hb0).2 k (List.mem_range.mpr hk0)
        simp only [gotSiteB, hi0] at this
        simp only [gotBefore_congr hpre]
        exact this
      | _ => rfl
  have hgb : gotB vcp t n = true := by
    simp only [gotB]
    refine (array_all_iff _ _).2 fun q vb hq => ?_
    simp only [Bool.and_eq_true]
    exact ⟨(array_all_iff _ _).2 fun k i hi => hdef q vb k i hq hi,
      List.all_eq_true.2 fun k _ => hsite q vb hq k⟩
  -- the GOT load before the call
  have hbef : gotBefore t n vb k = true := by
    have := hsite q vb hvb k
    rcases hk with hk | ⟨ti, hk⟩ <;> simpa [gotSiteB, hk, hdst] using this
  simp only [gotBefore, List.any_eq_true, List.mem_range, decide_eq_true_eq] at hbef
  obtain ⟨j, -, hj⟩ := hbef
  have hsym : gotSym vcp t = some n := by
    unfold gotSym
    refine findSome_eq (fun x hx m hm => ?_)
      ⟨MInst.loadExtNameGot (.vreg t .int) n, ?_, ?_⟩
    · simp only [List.mem_flatMap, Array.mem_toList_iff] at hx
      obtain ⟨vb', hvb', hx⟩ := hx
      obtain ⟨q', hq'⟩ := Array.getElem?_of_mem hvb'
      obtain ⟨k', hk'⟩ := Array.getElem?_of_mem hx
      have hd := hdef q' vb' k' x hq' hk'
      split at hm
      · rename_i t' n' 
        split at hm
        · rename_i ht
          subst ht
          cases hm
          obtain ⟨ops, hops, ho⟩ := operands_got t' m
          simp only [gotDefB, hops, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hd
          rcases hd with hd | hd
          · obtain ⟨o, hom, hod, hov⟩ := ho
            obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem hom
            have := Array.any_eq_false.mp hd i' (by simpa using hi')
            simp only [Array.getElem_toList] at hod hov
            exact absurd this (by simp [hod, hov])
          · cases hd; rfl
        · cases hm
      · cases hm
    · simp only [List.mem_flatMap, Array.mem_toList_iff]
      exact ⟨vb, Array.mem_of_getElem? hvb, Array.mem_of_getElem? hj⟩
    · simp
  unfold gotOf
  rw [hsym]
  simp [hgb]

/-! ## The call sites of the prepared VCode -/

theorem siteCall_prep {g : Clif.Function} {vc vcp : VCode} {isTry : Bool} {rets : Nat}
    {c : CallInfo} (h : SiteCall g vc isTry rets c)
    (hgot : ∀ t n, c.dest = .reg (.vreg t .int) → gotOf vc t = some n → gotOf vcp t = some n) :
    SiteCall g vcp isTry rets c := by
  obtain ⟨args, ⟨e, h1, h2, h3, h4⟩ | h⟩ := h
  · refine ⟨args, .inl ⟨e, h1, h2, h3, ?_⟩⟩
    rcases h4 with h4 | ⟨t, ht, hg⟩
    · exact .inl h4
    · exact .inr ⟨t, ht, hgot t _ ht hg⟩
  · exact ⟨args, .inr h⟩

/-- **Every call site of the prepared VCode is the call of a call site of `g`** (from the ISLE
inversion `CallShapeHyp` on `lowerFunction`'s VCode). -/
theorem siteCalls_of_lower (hH : CallShapeHyp) {p : Clif.Program} {g : Clif.Function}
    {vc vcp : VCode} (hsub : InSubset p g) (hd : Dominated g) (hs : LowerScope g)
    (hl : lowerFunction g = .ok vc) (hp : prepare vc = .ok vcp) {q : Nat} {vb : VBlock} {k : Nat}
    (hq : vcp.blocks[q]? = some vb) :
    (∀ c, vb.insts[k]? = some (.call c) → SiteCall g vcp false 0 c) ∧
    (∀ c ti, vb.insts[k]? = some (.tryCall c ti) → SiteCall g vcp true ti.rets c) := by
  have hdom := prepDomain_of_lower hs hl hs.nonempty
  refine ⟨fun c hi => ?_, fun c ti hi => ?_⟩
  · obtain ⟨b, vb0, hb, hi0, -⟩ := (prep_site hp hdom hq hi).1 c rfl
    exact siteCall_prep ((hH p g vc hsub hd hs hl b vb0 k hb).1 c hi0)
      fun t n hdst hg => gotOf_prep hp hdom hg hq (.inl hi) hdst
  · obtain ⟨b, vb0, ti0, hb, hi0, hr, -⟩ := (prep_site hp hdom hq hi).2 c ti rfl
    have := (hH p g vc hsub hd hs hl b vb0 k hb).2 c ti0 hi0
    rw [hr] at this
    exact siteCall_prep this fun t n hdst hg => gotOf_prep hp hdom hg hq (.inr ⟨ti, hi⟩) hdst

/-! ## The input condition at a call site -/

theorem dirSiteB_of {P : Clif.Program} {S : String → Option Nat} {g : Clif.Function}
    (hc : callScopeB P S g = true) {isTry : Bool} {args : List Nat} {e : Clif.ExtFunc}
    (h : DirSite g isTry args e) : dirSiteB P e args = true := by
  obtain ⟨fn, hfn, B, hB, ⟨-, st, hst, hi⟩ | ⟨-, et, ht⟩⟩ := h
  · have := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp hc B hB)
    have := List.all_eq_true.mp this.1 st hst
    simpa only [hi, hfn] using this
  · have := ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hc B hB)).2
    simpa only [ht, hfn] using this

theorem indSiteB_of {P : Clif.Program} {S : String → Option Nat} {g : Clif.Function}
    (hc : callScopeB P S g = true) {isTry : Bool} {args : List Nat} {s : Clif.Signature}
    (h : IndSite g isTry args s) : indSiteB P S g s args = true := by
  obtain ⟨B, hB, ⟨rfl, st, hst, sg, callee, hi, hs⟩ | ⟨rfl, callee, et, ht, hs⟩⟩ := h
  · have := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp hc B hB)
    have := List.all_eq_true.mp this.1 st hst
    simpa only [hi, hs] using this
  · have := ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hc B hB)).2
    simpa only [ht, hs] using this

theorem dirSite_decl {g : Clif.Function} {isTry : Bool} {args : List Nat} {e : Clif.ExtFunc}
    (h : DirSite g isTry args e) : e ∈ g.externs.map (·.2) := by
  obtain ⟨fn, hfn, -⟩ := h
  exact lookup_mem hfn

theorem decU_retPairs (L : List (Nat × Reg)) : decU (retPairs L) = L := by
  simp [decU, retPairs, Function.comp_def]

theorem decD_callDefs (D : List (Reg × Nat)) : decD (callDefs D) = D := by
  simp [decD, callDefs, Function.comp_def]

theorem take_xs {D : List (Reg × Nat)} (hD : D.map (·.1) = (List.range D.length).map Reg.x)
    (m : Nat) : (D.map (·.1)).take m = (List.range (min m D.length)).map Reg.x := by
  rw [hD, ← List.map_take, List.take_range]

/-! ## `siteOk` -/

/-- **A call site of `g`'s call `c` passes `siteOk`.** -/
theorem siteOk_of {P : Clif.Program} {S : String → Option Nat} {g : Clif.Function}
    (hnd : (P.funcs.map (·.name)).Nodup)
    (hc : callScopeB P S g = true) {vc : VCode} {isTry : Bool} {rets : Nat} {c : CallInfo}
    (h : SiteCall g vc isTry rets c) : siteOk P g (indToB S g) vc c = true := by
  obtain ⟨args, ⟨e, hds, ⟨L, D, hu, hdf, hL, hD⟩, -, hdest⟩ |
    ⟨s, his, ⟨L, D, hu, hdf, hL, hD⟩, -, t, hdest⟩⟩ := h
  · have hdir := dirSiteB_of hc hds
    have hdecl : g.externs.any (fun e' => e'.2.name == e.name) = true := by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (dirSite_decl hds)
      exact List.any_eq_true.mpr ⟨p, hp, by simp⟩
    obtain ⟨d, us, ds⟩ := c
    simp only at hu hdf hdest
    subst hu hdf
    rcases hdest with rfl | ⟨t, rfl, hgot⟩
    · unfold siteOk
      simp only
      cases hf : P.func? e.name with
      | none => rfl
      | some h =>
        obtain ⟨-, hhn⟩ := Clif.Program.func?_some hf
        simp only [dirSiteB, hf, decide_eq_true_eq] at hdir
        simp [hdecl, decU_retPairs, decD_callDefs, hL, hdir, take_xs hD]
    · unfold siteOk blrOk
      simp only [decU_retPairs, decD_callDefs, decide_true, Bool.true_and, List.all_eq_true,
        Bool.or_eq_true, Bool.not_eq_true', hgot, bne_iff_ne, ne_eq, decide_eq_true_eq,
        Bool.and_eq_true]
      intro h hh
      by_cases hn : h.name = e.name
      · have hf : P.func? e.name = some h := hn ▸ func?_of_mem hnd hh
        simp only [dirSiteB, hf, decide_eq_true_eq] at hdir
        exact .inr ⟨by rw [hL, hdir], take_xs hD _⟩
      · exact .inl (.inl (.inr hn))
  · have hind := indSiteB_of hc his
    obtain ⟨d, us, ds⟩ := c
    simp only at hu hdf hdest
    subst hu hdf hdest
    unfold siteOk blrOk
    simp only [decU_retPairs, decD_callDefs, decide_true, Bool.true_and, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, Bool.and_eq_true]
    intro h hh
    have := List.all_eq_true.mp hind h hh
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, Bool.and_eq_true] at this
    have hlen : (callRegs s args).length = L.length := by rw [← hL, List.length_map]
    rcases this with (h1 | h1) | h1
    · exact .inl (.inl (.inl h1))
    · exact .inl (.inr (by rwa [← hlen]))
    · exact .inr ⟨by rw [hL, h1], take_xs hD _⟩

/-! ## The theorem -/

/-- **The call sites of the compiler's own output** (`callRegs/blrRegs`): for an in-scope
function `g` of `P` passing the input condition `callScopeB P S g`, given the ISLE call
inversion `CallShapeHyp`. -/
theorem sites_of_lower (hH : CallShapeHyp) {P : Clif.Program} {S : String → Option Nat}
    {g : Clif.Function} {vc vcp : VCode}
    (hsub : InSubset P.bare g) (hd : dominatedB g = true) (hs : lowerScopeB g = true)
    (hnd : (P.funcs.map (·.name)).Nodup)
    (hc : callScopeB P S g = true)
    (hl : lowerFunction g = .ok vc) (hp : Backend.prepare vc = .ok vcp) :
    allInsts vcp (siteB (siteOk P g (indToB S g) vcp)) = true := by
  have hsc := fun {q vb k} (hq : vcp.blocks[q]? = some vb) =>
    siteCalls_of_lower (k := k) hH hsub (dominated_of hd) (lowerScope_of hs) hl hp hq
  refine (array_all_iff _ _).2 fun q vb hq => (array_all_iff _ _).2 fun k i hi => ?_
  cases i with
  | call c => exact siteOk_of hnd hc ((hsc hq).1 c hi)
  | tryCall c ti => exact siteOk_of hnd hc ((hsc hq).2 c ti hi)
  | _ => rfl

end E2E.LinkCheck
