import FV.Backend.Proof.LowerLoopRun
import FV.Backend.Proof.LowerTotalCtx
import FV.Backend.Proof.LowerTotalDefs
import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.SpillArity
import FV.Backend.Proof.EntryParams

/-!
# Totality of the lowering: the driver (V7)

`lowerFunction_ok`: on input in the scope of `E2E.LinkCheck.fnScopeB` (without `lowersB`) that
satisfies the new input conditions `driverInB`, `lowerFunction` succeeds whenever the ISLE runs
on `buildCtx`'s context make progress (`IselProg`, `LowerTotalDefs.lean`). The proof follows the
named loop bodies of `LowerLoopCode.lean` (`lowerFunction_eq`) and shows that no body returns
`.error`; `buildCtx_ok` (`LowerTotalCtx.lean`) does the same for `buildCtx`.

Every failure path of `lowerFunction` (`FV/Backend/Isel.lean`) and the hypothesis excluding it:

* calling convention of `f` (`throw "calling convention …"`) — `driverInB`: `aapcsConv`;
* `sigParamBytes` (an `i128`, non-`i64` `sret` or special-purpose parameter) — subset E (`sigE`)
  and `sigAbiOk`; `i128 return value` — subset E; `sret` with return values — `sigAbiOk`;
* `more than 8 return values` — `driverInB`: at most 8 returns;
* `buildCtx` — `buildCtx_ok` (see `LowerTotalCtx.lean` for its own paths);
* the entry's `sigArgLocs` (its length check included: `sretFold_size`) — as `sigParamBytes`;
* `unknown value` of an entry/block parameter, of a statement result, of a branch or `try_call`
  value argument; `value register is not virtual` — every value of `f` has the register
  `vreg v` (`CtxFacts.vals`), and every operand of a terminator is a value of `f`
  (`dominatedB`: it is available, `availOf_defs`);
* a statement's `lower` run failing, returning no `regsVec`, a wrong number of results or a
  multi-register result — `IselProg.stmt` (`StmtProg`);
* `tryCallData`/`exnTableOpnd` (undeclared signature, convention other than `system_v`,
  `context` items, undeclared callee, callee signature ≠ table signature) — `driverInB`
  (`tryInB`, `termInB`); `termData` of a `return_call` — subset E (`termE`);
* `sret parameter is not an entry-block parameter` — `entryParamsB` and a non-empty function
  (`lowerScopeB`): `sretBad_false`;
* `unknown block`/`argument count` of a `jump`/`brif`/`br_table` successor (`blockIdx`,
  `blockArgRegs`) — `driverInB` (the target exists: `termInB`) and `arityOkB` (the count);
* `try_call`: `more than 8 return values`, `returning i128` — `tryInB`; a successor's
  `unknown block`/`argument count` — `tryInB` (`tryDestInB`); `retN` on an exception edge,
  `exnN` on the normal edge, `exnN` out of range — `tryInB`; `retN` out of range —
  `lowerScopeB` (`LowerScope.tryRet`, `i < sig.returns.length ≤ (sigRets sig).length`);
  `successor count` (`tryInfoOf`) — `tryInB` (no `context` items: one handler per item);
* a terminator's `lower`/`lower_branch` run failing or returning no value — `IselProg.term`
  (`TermProg`) and `IselProg.try_` (`TryProg`); a `try_call` lowering not ending in a call —
  `TryProg`.

`driverInB_witness`: the conditions hold on the loop witness of `FV/E2E/LowerDirect.lean`
(`lowerWitnessSrc`, as a literal) and on a witness with a `load`, a `call` and a `try_call`.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-! ## The input conditions -/

/-- A `try_call` successor's block exists and takes as many parameters as it gets arguments
(Cranelift's verifier: `verify_block_call`, the destination's parameter count). -/
def tryDestInB (f : Clif.Function) (td : Clif.TryDest) : Bool :=
  match f.block? td.block with
  | some tb => tb.params.length == td.args.length
  | none => false

/-- **The exception-table conditions** of a `try_call`/`try_call_indirect` — input restrictions
mirroring Cranelift's verifier and aarch64 ABI:

* the table's signature is declared (`verify_exception_table`), with integer parameters and
  returns (`sigIntB`: the lowering's calls pass integers only), the `system_v` (or default)
  convention (Cranelift 0.136.1 panics on a `fast` callee; `tail`/`preserve_all` are not lowered
  here), at most 8 returns (the aarch64 return registers x0..x7 without
  `enable_multi_ret_implicit_sret`) and no `i128` return (legalized away before lowering);
* no `context` items (Wasmtime's dynamic contexts; cg_clif never emits them);
* every successor exists with as many parameters as arguments (`tryDestInB`);
* a handler passes no `retN` and only `exnN` with `N < 2` (the `system_v` payload registers x0,
  x1: `exception_payload_regs`); the normal return passes no `exnN` (Cranelift's verifier: the
  `BlockArg::TryCallRet`/`TryCallExn` placement rules). -/
def tryInB (f : Clif.Function) (et : Clif.ExnTable) : Bool :=
  match f.sigDecls.lookup et.sig with
  | none => false
  | some s =>
    sigIntB s && (s.callConv.isNone || s.callConv == some .systemV) && decide (s.returns.length ≤ 8) &&
    s.returns.all (·.ty != .i128) &&
    et.items.all (fun | .context _ => false | _ => true) &&
    et.handlers.all (fun td => tryDestInB f td && td.args.all fun
      | .ret _ => false
      | .exn i => decide (i < 2)
      | .val _ => true) &&
    tryDestInB f et.normal && et.normal.args.all fun
      | .exn _ => false
      | _ => true

/-- **The terminator conditions**: a `try_call`'s exception table (`tryInB`) and its callee is
declared with the table's signature (Cranelift's verifier: the `try_call`'s `sigN` is the
callee's signature); a `jump`/`brif`/`br_table` successor exists (`verify_block_call`). -/
def termInB (f : Clif.Function) : Clif.Terminator → Bool
  | .tryCall fn _ et => tryInB f et && match f.extern? fn, f.sigDecls.lookup et.sig with
    | some e, some s => e.sig == s
    | _, _ => false
  | .tryCallIndirect _ _ et => tryInB f et
  | t => (dests t).all fun bc => (f.block? bc.block).isSome

/-- **The driver's input conditions** (the new ones; the rest of `lowerFunction_ok`'s hypotheses
are conjuncts of `E2E.LinkCheck.fnScopeB`): the function's calling convention is AAPCS64
(`system_v`, `fast` or the default: the conventions the aarch64 backend lowers as AAPCS64), it
has at most 8 return values (the aarch64 return registers x0..x7 without
`enable_multi_ret_implicit_sret`), every statement satisfies `stmtInB` and every terminator
`termInB`. Each mirrors a check `lowerFunction`/`buildCtx` makes on the way, so it rejects no
function they accept. -/
def driverInB (f : Clif.Function) : Bool :=
  aapcsConv f.sig.callConv && decide (f.sig.returns.length ≤ 8) &&
  f.blocks.all fun B => B.body.all (stmtInB f) && termInB f B.term

/-! ## Loops -/

/-- A loop whose body yields on every element, keeping an invariant indexed by the number of
elements done, succeeds. -/
theorem forIn_ok {ε α β : Type} (body : α → β → Except ε (ForInStep β)) (P : Nat → β → Prop) :
    ∀ (l : List α) (k : Nat) (init : β), P k init →
      (∀ x ∈ l, ∀ j b, P j b → ∃ b', body x b = .ok (.yield b') ∧ P (j + 1) b') →
      ∃ r, forIn l init body = .ok r ∧ P (k + l.length) r
  | [], k, init, h, _ => ⟨init, rfl, by simpa using h⟩
  | a :: l, k, init, h, hb => by
    obtain ⟨b', hb', hP⟩ := hb a List.mem_cons_self k init h
    rw [List.forIn_cons, hb']
    obtain ⟨r, hr, hPr⟩ := forIn_ok body P l (k + 1) b' hP fun x hx => hb x (List.mem_cons_of_mem _ hx)
    exact ⟨r, hr, by rw [List.length_cons]; rwa [show k + (l.length + 1) = k + 1 + l.length by omega]⟩

/-- `forIn_ok` without an invariant. -/
theorem forIn_ok' {ε α β : Type} (body : α → β → Except ε (ForInStep β)) (l : List α) (init : β)
    (hb : ∀ x ∈ l, ∀ b, ∃ b', body x b = .ok (.yield b')) : ∃ r, forIn l init body = .ok r := by
  obtain ⟨r, hr, -⟩ := forIn_ok body (fun _ _ => True) l 0 init trivial
    fun x hx _ b _ => (hb x hx b).imp fun _ h => ⟨h, trivial⟩
  exact ⟨r, hr⟩

/-- `mapM` succeeds when every element does. -/
theorem lmapM_ok' {ε α β : Type} {g : α → Except ε β} :
    ∀ (l : List α), (∀ x ∈ l, ∃ y, g x = .ok y) → ∃ ys, l.mapM g = .ok ys
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨y, hy⟩ := h a List.mem_cons_self
    obtain ⟨ys, hys⟩ := lmapM_ok' l fun x hx => h x (List.mem_cons_of_mem _ hx)
    refine ⟨y :: ys, ?_⟩
    simp [List.mapM_cons, hy, hys, bind, Except.bind, pure, Except.pure]

theorem amapM_ok' {ε α β : Type} {g : α → Except ε β} (l : List α)
    (h : ∀ x ∈ l, ∃ y, g x = .ok y) : ∃ ys, l.toArray.mapM g = .ok ys := by
  obtain ⟨ys, hys⟩ := lmapM_ok' l h
  refine ⟨ys.toArray, ?_⟩
  rw [Array.mapM_eq_mapM_toList, List.toList_toArray, hys]; rfl

/-! ## The ABI -/

/-- `sigArgs` computes on a `sigAbiOk` signature without `i128` parameters. -/
theorem sigArgs_ok {s : Clif.Signature} (hA : sigAbiOk s = true)
    (hE : s.params.all (Compile.tyE ·.ty) = true) : ∃ bytes, sigArgs s = .ok bytes := by
  unfold sigArgs
  refine lmapM_ok' _ fun p hp => ?_
  simp only [sigAbiOk, Bool.and_eq_true, List.all_eq_true] at hA
  have h1 := hA.1.1.1 p hp
  have h2 : p.ty ≠ .i128 := by
    have := List.all_eq_true.mp hE p hp
    simp only [Compile.tyE, Bool.and_eq_true, bne_iff_ne] at this
    exact this.2
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h1
  rcases h1 with h1 | ⟨h1, h3⟩ <;> simp [pure, Except.pure, *]

theorem sigRets_le {s : Clif.Signature} (h : s.returns.length ≤ 8) : (sigRets s).length ≤ 8 := by
  unfold sigRets
  split
  · split <;> simp_all
  · exact h

theorem returns_le_sigRets (s : Clif.Signature) : s.returns.length ≤ (sigRets s).length := by
  unfold sigRets
  split
  · split
    · rename_i h; simp [List.isEmpty_iff.mp h]
    · exact Nat.le_refl _
  · exact Nat.le_refl _

theorem foldl_size {α γ : Type} (g : Array Reg × γ → α → Array Reg × γ)
    (hg : ∀ q a, (g q a).1.size = q.1.size + 1) :
    ∀ (l : List α) (q : Array Reg × γ), (l.foldl g q).1.size = q.1.size + l.length
  | [], _ => rfl
  | a :: l, q => by
    rw [List.foldl_cons, foldl_size g hg l, hg]
    simp; omega

/-- `tryRegsOf` computes for a callee with at most 8 returns: one vreg per declared return, one
per payload register. -/
theorem tryRegsOf_ok {s : Clif.Signature} (h : s.returns.length ≤ 8) (st : LState) :
    ∃ rets pays st', tryRegsOf s st = some ((rets, pays), st') ∧
      rets.length = s.returns.length ∧ pays.length = (payloadRegs s.callConv).length := by
  unfold tryRegsOf
  simp only [retRegs, h, ite_true, bind, Option.bind, pure]
  refine ⟨_, _, _, rfl, ?_, ?_⟩
  · rw [Array.length_toList, foldl_size _ (fun q a => by rcases q; simp)]
    simp
  · rw [Array.length_toList, foldl_size _ (fun q a => by rcases q; simp; split <;> simp)]
    simp

/-! ## Values -/

/-- An available value is a value of `f`. -/
theorem availOf_defs {f : Clif.Function} {ctx : Ctx} {bi j y : Nat}
    (h : y ∈ availOf f (availIn f ctx) bi j) : y ∈ valueDefs f := by
  obtain ⟨B, hB, hm, -⟩ := mem_availOf.mp h
  have hBm := List.mem_of_getElem? hB
  simp only [List.mem_append] at hm
  rcases hm with (hm | hm) | hm
  · simp only [valueDefs, List.mem_flatMap, List.mem_append]
    exact ⟨B, hBm, .inl hm⟩
  · exact ((inFix_fixOk (f := f) (ctx := ctx) (gn := id)).cand bi y hm).2.2.2.1
  · simp only [valueDefs, List.mem_flatMap, List.mem_append]
    refine ⟨B, hBm, .inr ?_⟩
    simp only [defsBefore, List.mem_flatMap] at hm
    obtain ⟨s, hs, hy⟩ := hm
    exact ⟨s, List.mem_of_mem_take hs, hy⟩

theorem dests_args_mem {f : Clif.Function} {t : Clif.Terminator} {bc : Clif.BlockCall}
    (hbc : bc ∈ dests t) {a : Nat} (ha : a ∈ bc.args) : a ∈ termArgs (abiTerm f t) := by
  cases t with
  | jump d => simp_all [dests, termArgs, abiTerm]
  | brif c th el =>
    simp only [dests, List.mem_cons, List.not_mem_nil, or_false] at hbc
    rcases hbc with rfl | rfl <;> simp [termArgs, abiTerm, ha]
  | brTable x d tbl =>
    simp only [dests, List.mem_cons] at hbc
    rcases hbc with rfl | hbc
    · simp [termArgs, abiTerm, ha]
    · simp only [termArgs, abiTerm, List.mem_cons, List.mem_append, List.mem_flatMap]
      exact .inr ⟨bc, hbc, ha⟩
  | _ => simp [dests] at hbc

theorem exn_vals_mem {et : Clif.ExnTable} {td : Clif.TryDest} (htd : td ∈ et.dests) {v : Nat}
    (hv : Clif.TryArg.val v ∈ td.args) : v ∈ et.vals := by
  have hvd : v ∈ td.vals := List.mem_filterMap.mpr ⟨_, hv, rfl⟩
  simp only [Clif.ExnTable.dests, List.mem_append, List.mem_singleton] at htd
  simp only [Clif.ExnTable.vals, List.mem_append, List.mem_flatMap]
  rcases htd with htd | rfl
  · right
    simp only [Clif.ExnTable.handlers, List.mem_filterMap] at htd
    obtain ⟨it, hit, he⟩ := htd
    refine ⟨it, hit, ?_⟩
    cases it <;> simp_all
  · exact .inl hvd

theorem try_vals_mem {f : Clif.Function} {t : Clif.Terminator} {et : Clif.ExnTable}
    (ht : IsTryWith t et) {td : Clif.TryDest} (htd : td ∈ et.dests) {v : Nat}
    (hv : Clif.TryArg.val v ∈ td.args) : v ∈ termArgs (abiTerm f t) := by
  have := exn_vals_mem htd hv
  rcases ht with ⟨fn, args, rfl⟩ | ⟨c, args, rfl⟩ <;> simp [termArgs, abiTerm, this]

/-! ## Blocks -/

theorem blockIdx_of_block {f : Clif.Function} {b : Nat} {tb : Clif.Block}
    (h : f.block? b = some tb) : ∃ tl, blockIdxE f b = .ok tl := by
  have h1 : (f.blocks.find? (·.id == b)).isSome = true := by
    unfold Clif.Function.block? at h; rw [h]; rfl
  obtain ⟨x, hx, hp⟩ := List.find?_isSome.mp h1
  have h2 : (f.blocks.findIdx? (·.id == b)).isSome = true := by
    rw [List.findIdx?_isSome]; exact List.any_eq_true.mpr ⟨x, hx, hp⟩
  obtain ⟨tl, htl⟩ := Option.isSome_iff_exists.mp h2
  exact ⟨tl, blockIdxE_of htl⟩

theorem blockArgRegs_ok' {f : Clif.Function} {ctx : Ctx} {bc : Clif.BlockCall} {tb : Clif.Block}
    (htb : f.block? bc.block = some tb) (hn : tb.params.length = bc.args.length)
    (hr : ∀ a ∈ bc.args, ctx.valueReg? a = some (.vreg a .int)) :
    ∃ args, blockArgRegs ctx f bc = .ok args := by
  unfold blockArgRegs
  simp only [htb, hn, bne_self_eq_false, Bool.false_eq_true, ite_false, bind, Except.bind]
  obtain ⟨ys, hys⟩ := amapM_ok' (g := fun a => match ctx.valueReg? a with
    | some r => (pure r : Except String Reg)
    | none => throw s!"unknown value v{a}") bc.args fun a ha => by
      simp [hr a ha, pure, Except.pure]
  exact ⟨ys, hys⟩

/-! ## The loop bodies -/

/-- The results loop of a statement succeeds on single-register results. -/
theorem resLoop_ok {ctx : Ctx} (results : List Nat) (rss : List (List Reg))
    (hr : ∀ r ∈ results, ctx.valueReg? r = some (.vreg r .int)) (hl : ∀ rs ∈ rss, rs.length = 1)
    (s : DState × Array MInst) : ∃ q, forIn (results.zip rss) s (resBody ctx) = .ok q := by
  refine forIn_ok' _ _ _ fun x hx b => ?_
  obtain ⟨r, rs⟩ := x
  have hr' := hr r (List.of_mem_zip hx).1
  obtain ⟨o, rfl⟩ := List.length_eq_one_iff.mp (hl rs (List.of_mem_zip hx).2)
  cases o <;> simp [resBody, hr', pure, Except.pure]

/-- A statement's lowering never fails: the ISLE run is `StmtProg`'s. -/
theorem stmtBody_ok {ctx : Ctx} (hP : StmtProg ctx) {i : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[i]? = some info) (hc : info.clif = some inst)
    (hr : ∀ r ∈ info.results, ctx.valueReg? r = some (.vreg r .int)) (s : DState × Array MInst) :
    ∃ s', stmtBody ctx i s = .ok (.yield s') := by
  obtain ⟨rss, s', tr, hrun, hlen⟩ := hP i info inst { s.1.st with emitted := #[] } hi hc
  unfold stmtBody
  simp only [bind, Except.bind, hrun, getElem!_of hi]
  by_cases he : info.results = []
  · simp only [he, List.isEmpty_nil, Bool.not_true, Bool.and_false, Bool.false_eq_true,
      ite_false, List.zip_nil_left, List.forIn_nil, pure, Except.pure]
    exact ⟨_, rfl⟩
  · obtain ⟨hl1, hl2⟩ := hlen he
    obtain ⟨q, hq⟩ := resLoop_ok (ctx := ctx) info.results rss hr hl2 (s.1, #[])
    simp only [hl1, bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ite_false, hq,
      pure, Except.pure]
    exact ⟨_, rfl⟩

/-- The entry block's argument setup never fails on parameters with registers. -/
theorem entryLoop_ok {ctx : Ctx} (l : List (((Clif.ValueId × Clif.Ty) × ArgLoc) × Nat))
    (hr : ∀ x ∈ l, ∃ r, ctx.valueReg? x.1.1.1 = some r) (s : Array MInst × Array (Reg × Reg)) :
    ∃ q, forIn l s (entryBody ctx) = .ok q := by
  refine forIn_ok' _ _ _ fun x hx b => ?_
  obtain ⟨r, hr⟩ := hr x hx
  obtain ⟨⟨⟨v, t⟩, loc⟩, bytes⟩ := x
  cases loc <;> simp_all [entryBody, pure, Except.pure]

/-- A branch successor's edge never fails; it adds one target. -/
theorem destBody_ok {f : Clif.Function} {ctx : Ctx} {bc : Clif.BlockCall} {tb : Clif.Block}
    (htb : f.block? bc.block = some tb) (hn : tb.params.length = bc.args.length)
    (hr : ∀ a ∈ bc.args, ctx.valueReg? a = some (.vreg a .int)) (s : DState × Array Label) :
    ∃ s', destBody f ctx bc s = .ok (.yield s') ∧ s'.2.size = s.2.size + 1 := by
  obtain ⟨tl, htl⟩ := blockIdx_of_block htb
  unfold destBody
  simp only [bind, Except.bind, htl]
  split
  · exact ⟨_, rfl, by simp⟩
  · obtain ⟨args, ha⟩ := blockArgRegs_ok' htb hn hr
    simp only [ha, pure, Except.pure]
    exact ⟨_, rfl, by simp⟩

/-- A `try_call` successor argument that `ArgOk` accepts has a register. -/
theorem tryArgE_ok' {ctx : Ctx} {rets pays : Array Reg} {nh k : Nat} {a : Clif.TryArg}
    (h : ArgOk ctx nh rets.size pays.size k a) : ∃ r, tryArgE ctx rets pays nh k a = .ok r := by
  cases a with
  | val v => simp only [ArgOk] at h; simp [tryArgE, h, pure, Except.pure]
  | ret i =>
    simp only [ArgOk] at h
    simp [tryArgE, h.1, Array.getElem?_eq_getElem h.2, pure, Except.pure]
  | exn i =>
    simp only [ArgOk] at h
    simp [tryArgE, h.1, Array.getElem?_eq_getElem h.2, pure, Except.pure]

/-- A `try_call` successor's edge never fails; it adds one target. -/
theorem tryBody_ok {f : Clif.Function} {ctx : Ctx} {rets pays : Array Reg} {nh k : Nat}
    {td : Clif.TryDest} (h : TryDestOk f ctx nh rets.size pays.size k td)
    (s : DState × Array Label) :
    ∃ s', tryBody f ctx rets pays nh (td, k) s = .ok (.yield s') ∧ s'.2.size = s.2.size + 1 := by
  obtain ⟨⟨tb, htb, hn⟩, ha⟩ := h
  obtain ⟨tl, htl⟩ := blockIdx_of_block htb
  obtain ⟨args, hargs⟩ := amapM_ok' (g := tryArgE ctx rets pays nh k) td.args
    fun a hm => tryArgE_ok' (ha a hm)
  unfold tryBody
  simp only [bind, Except.bind, htl, htb, hn, bne_self_eq_false, Bool.false_eq_true, ite_false,
    hargs, pure, Except.pure]
  exact ⟨_, rfl, by simp⟩

/-- `mapM` does not fail when every element succeeds. -/
theorem amapM_ne_error {ε α β : Type} {g : α → Except ε β} {l : List α} {e : ε}
    (h : ∀ x ∈ l, ∃ y, g x = .ok y) (he : l.toArray.mapM g = .error e) : False := by
  obtain ⟨ys, hys⟩ := amapM_ok' l h
  rw [hys] at he; cases he

/-- A block's parameters never fail. -/
theorem paramsPart_ok' {ctx : Ctx} {b : Clif.Block} {bi : Nat} {code : Array MInst} {d : DState}
    {st : LState} {n : List Isle.RuleId} {jumpArgs : Array Reg} {emitted : Array MInst}
    (hpar : ∀ q ∈ b.params, ∃ r, ctx.valueReg? q.1 = some r) :
    ∃ d', paramsPart ctx b bi code d st n jumpArgs emitted = .ok (.yield d') := by
  unfold paramsPart
  split
  · exact ⟨_, rfl⟩
  · simp only [bind, Except.bind]
    split
    · rename_i e he
      refine (amapM_ne_error (fun q hq => ?_) he).elim
      obtain ⟨r, hr⟩ := hpar q hq
      simp [hr, pure, Except.pure]
    · exact ⟨_, rfl⟩

/-- The end of a block never fails once the terminator's ISLE run returns a value (ending in a
call for a `try_call`). -/
theorem finishBlock_ok' {ctx : Ctx} {b : Clif.Block} {bi ti : Nat} {code : Array MInst}
    {d : DState} {ctx' : Ctx} {targets : Array Label} {jumpArgs : Array Reg}
    {tryInfo : Option TryInfo} {v : V} {st : LState} {n : List Isle.RuleId}
    (hrun : runTerm ctx' (termCall b.term ti targets.toList).1 (termCall b.term ti targets.toList).2
      { d.st with emitted := #[] } = .ok (some v, st, n))
    (hlast : ∀ t, tryInfo = some t → ∃ c, st.emitted.back? = some (.call c))
    (hpar : ∀ q ∈ b.params, ∃ r, ctx.valueReg? q.1 = some r) :
    ∃ d', finishBlock ctx b bi ti code d ctx' targets jumpArgs tryInfo = .ok (.yield d') := by
  unfold finishBlock
  rw [termArgsOf_eq]
  generalize termCall b.term ti targets.toList = tc at hrun ⊢
  obtain ⟨term, args⟩ := tc
  simp only at hrun ⊢
  simp only [bind, Except.bind, hrun, Option.isNone_some, Bool.false_eq_true, ite_false]
  cases tryInfo with
  | none => exact paramsPart_ok' hpar
  | some t =>
    obtain ⟨c, hc⟩ := hlast t rfl
    simp only [hc]
    exact paramsPart_ok' hpar

/-- What the driver needs of a `try_call`'s exception table. -/
structure TryOk (f : Clif.Function) (ctx : Ctx) (et : Clif.ExnTable) (sig : Clif.Signature)
    (items : List (Option Nat)) : Prop where
  opnd : exnTableOpnd f et = .ok (sig, items)
  rets : sig.returns.length ≤ 8
  i128 : (sig.returns.any fun x => x.ty == Clif.Ty.i128) = false
  items : items.length = et.handlers.length
  dests : ∀ k td, et.dests[k]? = some td →
    TryDestOk f ctx et.handlers.length sig.returns.length (payloadRegs sig.callConv).length k td

theorem exnOf_of {t : Clif.Terminator} {et : Clif.ExnTable} (h : IsTryWith t et) :
    exnOf t = some et := by
  rcases h with ⟨fn, args, rfl⟩ | ⟨c, args, rfl⟩ <;> rfl

theorem termCall_try {t : Clif.Terminator} {et : Clif.ExnTable} (h : IsTryWith t et) (ti : Nat)
    (ls : List Label) : termCall t ti ls = ("lower_branch", [.inst ti, .labels ls]) := by
  rcases h with ⟨fn, args, rfl⟩ | ⟨c, args, rfl⟩ <;> rfl

/-- A `try_call` terminator never fails: the ISLE run is `TryProg`'s. -/
theorem tryTerm_ok {f : Clif.Function} {ctx : Ctx} (hP : TryProg f ctx) {b : Clif.Block}
    (hb : b ∈ f.blocks) {bi ti : Nat} (hti : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    {code : Array MInst} {d : DState} {data : V} {et : Clif.ExnTable} (het : IsTryWith b.term et)
    (hdata : tryCallData f b.term = .ok data) {sig : Clif.Signature} {items : List (Option Nat)}
    (hT : TryOk f ctx et sig items) (hpar : ∀ q ∈ b.params, ∃ r, ctx.valueReg? q.1 = some r) :
    ∃ d', tryTerm f ctx b bi ti code d (termCtx ctx ti data) et = .ok (.yield d') := by
  obtain ⟨rets, pays, st', hreg, hrl, hpl⟩ := tryRegsOf_ok hT.rets d.st
  have hregC : tryRegsOfC sig d.st = some ((rets, pays), st') := by
    rw [tryRegsOfC_eq (sigRets_classes_int (sigIntB_iff.mp (exnTableOpnd_int hT.opnd)).2)]
    exact hreg
  unfold tryTerm
  simp only [bind, Except.bind, exnTableOpndC_of hT.opnd, hregC, hT.i128, Bool.false_eq_true,
    ite_false]
  obtain ⟨s, hs, hsz⟩ := forIn_ok (tryBody f ctx rets.toArray pays.toArray et.handlers.length)
    (fun j (s : DState × Array Label) => s.2.size = j) et.dests.zipIdx 0 ({ d with st := st' }, #[])
    rfl (fun x hx j s hj => by
      obtain ⟨td, k⟩ := x
      have hk := List.mem_zipIdx_iff_getElem?.mp hx
      have h := hT.dests k td hk
      have e1 : rets.toArray.size = rets.length := by simp
      have e2 : pays.toArray.size = pays.length := by simp
      rw [← hrl, ← hpl, ← e1, ← e2] at h
      obtain ⟨s', h1, h2⟩ := tryBody_ok h s
      exact ⟨s', h1, by rw [h2, hj]⟩)
  rw [hs]
  simp only [List.length_zipIdx, Nat.zero_add] at hsz
  have hlen : s.2.toList.length = items.length + 1 := by
    rw [Array.length_toList, hsz, hT.items]; simp [Clif.ExnTable.dests]
  have hti' : ti < ctx.insts.size := (Array.getElem?_eq_some_iff.mp hti).1
  obtain ⟨v, s', tr, c, hrun, hc⟩ := hP ti b.term et data sig items (rets, pays) d.st st'
    s.2.toList { s.1.st with emitted := #[] } hti' hti ⟨b, hb, rfl⟩ (exnOf_of het) hdata hT.opnd
    hreg hlen
  simp only [tryInfoOf, hlen, bne_self_eq_false, Bool.false_eq_true, ite_false]
  refine finishBlock_ok' (v := v) (st := s') (n := tr) ?_ (fun _ _ => ⟨c, hc⟩) hpar
  rw [termCall_try het]
  simpa [tryCallF, tryCtx] using hrun

/-- A terminator's lowering never fails: the ISLE runs are `TermProg`'s and `TryProg`'s. -/
theorem termPart_ok' {f : Clif.Function} {ctx : Ctx} (hP : IselProg f ctx) {b : Clif.Block}
    (hb : b ∈ f.blocks) {bi stop : Nat}
    (hti : ctx.insts[stop - 1]? = some ⟨.op .unit, [], [], none⟩) {code : Array MInst}
    {d : DState} {data : V} (hdata : DataOk f b.term data) (hsret : sretBad f b.term = false)
    (hdests : ∀ bc ∈ dests b.term, ∃ tb, f.block? bc.block = some tb ∧
      tb.params.length = bc.args.length ∧ ∀ a ∈ bc.args, ctx.valueReg? a = some (.vreg a .int))
    (htry : ∀ et, IsTryWith b.term et → ∃ sig items, TryOk f ctx et sig items)
    (hpar : ∀ q ∈ b.params, ∃ r, ctx.valueReg? q.1 = some r) :
    ∃ d', termPart f ctx b bi stop code d data = .ok (.yield d') := by
  have hti' : stop - 1 < ctx.insts.size := (Array.getElem?_eq_some_iff.mp hti).1
  unfold termPart
  rw [hsret]
  simp only [Bool.false_eq_true, ite_false]
  split
  · rename_i bc heq
    obtain ⟨tb, htb, hn, hr⟩ := hdests bc (by rw [heq]; simp [dests])
    obtain ⟨ja, hja⟩ := blockArgRegs_ok' htb hn hr
    obtain ⟨tl, htl⟩ := blockIdx_of_block htb
    simp only [bind, Except.bind, hja, htl]
    have hd : termData (abiTerm f b.term) = .ok data := by
      rw [heq] at hdata ⊢; exact hdata
    obtain ⟨v, s', tr, hrun⟩ := hP.term (stop - 1) b.term data [tl] { d.st with emitted := #[] }
      hti' hti ⟨b, hb, rfl⟩ (by rw [heq]; rfl) hd (by rw [heq]; rfl)
    exact finishBlock_ok' (v := v) (st := s') (n := tr) hrun (fun _ h => nomatch h) hpar
  · rename_i fn args et heq
    have het : IsTryWith b.term et := .inl ⟨fn, args, heq⟩
    obtain ⟨sig, items, hT⟩ := htry et het
    have hd : tryCallData f b.term = .ok data := by
      rw [heq] at hdata ⊢; exact hdata
    exact tryTerm_ok hP.try_ hb hti het hd hT hpar
  · rename_i c args et heq
    have het : IsTryWith b.term et := .inr ⟨c, args, heq⟩
    obtain ⟨sig, items, hT⟩ := htry et het
    have hd : tryCallData f b.term = .ok data := by
      rw [heq] at hdata ⊢; exact hdata
    exact tryTerm_ok hP.try_ hb hti het hd hT hpar
  · rename_i h1 h2 h3
    have hnt : b.term.isTry = false := by
      cases ht : b.term with
      | tryCall fn args et => exact absurd ht (h2 fn args et)
      | tryCallIndirect c args et => exact absurd ht (h3 c args et)
      | _ => rfl
    have hd : termData (abiTerm f b.term) = .ok data := by
      unfold DataOk at hdata
      split at hdata
      · rename_i fn args et ht; exact absurd ht (h2 fn args et)
      · rename_i c args et ht; exact absurd ht (h3 c args et)
      · exact hdata
    obtain ⟨s, hs, hsz⟩ := forIn_ok (destBody f ctx) (fun j (s : DState × Array Label) => s.2.size = j)
      (destsOf b.term) 0 (d, #[]) rfl (fun bc hbc j s hj => by
        rw [destsOf_eq] at hbc
        obtain ⟨tb, htb, hn, hr⟩ := hdests bc hbc
        obtain ⟨s', h1, h2⟩ := destBody_ok htb hn hr s
        exact ⟨s', h1, by rw [h2, hj]⟩)
    simp only [bind, Except.bind, hs]
    obtain ⟨v, s', tr, hrun⟩ := hP.term (stop - 1) b.term data s.2.toList
      { s.1.st with emitted := #[] } hti' hti ⟨b, hb, rfl⟩ hnt hd (by simp [hsz])
    exact finishBlock_ok' (v := v) (st := s') (n := tr) hrun (fun _ h => nomatch h) hpar

/-- A block's statements and terminator never fail. -/
theorem bodyPart_ok' {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (sp : CtxSpec f ctx ranges st0) (hE : CtxE ctx) (hP : IselProg f ctx) {bi : Nat} {B : Clif.Block}
    (hB : f.blocks[bi]? = some B) (hdata : ∃ data, DataOk f B.term data)
    (hsret : sretBad f B.term = false)
    (hdests : ∀ bc ∈ dests B.term, ∃ tb, f.block? bc.block = some tb ∧
      tb.params.length = bc.args.length ∧ ∀ a ∈ bc.args, ctx.valueReg? a = some (.vreg a .int))
    (htry : ∀ et, IsTryWith B.term et → ∃ sig items, TryOk f ctx et sig items)
    (hpar : ∀ q ∈ B.params, ∃ r, ctx.valueReg? q.1 = some r) (d : DState) (code : Array MInst) :
    ∃ d', bodyPart f ctx B bi (blockStart f bi) (blockStart f bi + B.body.length + 1) d code =
      .ok (.yield d') := by
  have hBm := List.mem_of_getElem? hB
  have hti : ctx.insts[blockStart f bi + B.body.length + 1 - 1]? =
      some ⟨.op .unit, [], [], none⟩ := by
    rw [Nat.add_sub_cancel]; exact sp.facts.term bi B hB
  obtain ⟨data, hd⟩ := hdata
  unfold bodyPart
  simp only [bind, Except.bind]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.add_sub_cancel_left, Nat.add_one_sub_one, Nat.div_one]
  obtain ⟨s, hs⟩ := forIn_ok' (stmtBody ctx) (List.range' (blockStart f bi) B.body.length) (d, code)
    (fun i hi s => by
      obtain ⟨h1, h2⟩ := List.mem_range'_1.mp hi
      obtain ⟨j, rfl⟩ : ∃ j, i = blockStart f bi + j := ⟨i - blockStart f bi, by omega⟩
      have hj : j < B.body.length := by omega
      obtain ⟨info, hinfo, hc, hr⟩ := sp.facts.stmt bi B j _ hB (List.getElem?_eq_getElem hj)
      refine stmtBody_ok hP.stmt hinfo hc (fun r hr' => ?_) s
      rw [hr] at hr'
      refine (sp.facts.vals_int hE r ?_).2
      simp only [valueDefs, List.mem_flatMap, List.mem_append]
      exact ⟨B, hBm, .inr ⟨_, List.getElem_mem hj, hr'⟩⟩)
  rw [hs]
  dsimp only
  split
  · rename_i fn args et heq
    have hd' : tryCallData f B.term = .ok data := by
      unfold DataOk at hd; rw [heq] at hd ⊢; exact hd
    simp only [tryCallDataC_of hd']
    exact termPart_ok' hP hBm hti (by rwa [heq] at hd ⊢) hsret hdests htry hpar
  · rename_i c args et heq
    have hd' : tryCallData f B.term = .ok data := by
      unfold DataOk at hd; rw [heq] at hd ⊢; exact hd
    simp only [tryCallDataC_of hd']
    exact termPart_ok' hP hBm hti (by rwa [heq] at hd ⊢) hsret hdests htry hpar
  · rename_i h2 h3
    have hd' : termData (abiTerm f B.term) = .ok data := by
      unfold DataOk at hd
      split at hd
      · rename_i fn args et ht; exact absurd ht (h2 fn args et)
      · rename_i c args et ht; exact absurd ht (h3 c args et)
      · exact hd
    simp only [hd']
    exact termPart_ok' hP hBm hti hd hsret hdests htry hpar

/-- A block's lowering never fails. -/
theorem blockBody_ok' {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (sp : CtxSpec f ctx ranges st0) (hE : CtxE ctx) (hP : IselProg f ctx) {paramBytes : List Nat} {bi : Nat}
    {B : Clif.Block} (hB : f.blocks[bi]? = some B)
    (hent : ∃ locs n, sigArgLocs f.sig = .ok (locs, n)) (hdata : ∃ data, DataOk f B.term data)
    (hsret : sretBad f B.term = false)
    (hdests : ∀ bc ∈ dests B.term, ∃ tb, f.block? bc.block = some tb ∧
      tb.params.length = bc.args.length ∧ ∀ a ∈ bc.args, ctx.valueReg? a = some (.vreg a .int))
    (htry : ∀ et, IsTryWith B.term et → ∃ sig items, TryOk f ctx et sig items)
    (hpar : ∀ q ∈ B.params, ∃ r, ctx.valueReg? q.1 = some r) (d : DState) :
    ∃ d', blockBody f ctx ranges paramBytes (B, bi) d = .ok (.yield d') := by
  unfold blockBody
  simp only [getElem!_of (sp.ranges bi B hB)]
  split
  · obtain ⟨locs, n, hl⟩ := hent
    simp only [bind, Except.bind, hl]
    obtain ⟨s, hs⟩ := entryLoop_ok (ctx := ctx) ((B.params.zip locs).zip paramBytes)
      (fun x hx => hpar _ (List.of_mem_zip (List.of_mem_zip hx).1).1) (#[], #[])
    rw [hs]
    exact bodyPart_ok' sp hE hP hB hdata hsret hdests htry hpar _ _
  · exact bodyPart_ok' sp hE hP hB hdata hsret hdests htry hpar _ _

/-! ## From the input conditions to the loop hypotheses -/

theorem lmapM_ne_error {ε α β : Type} {g : α → Except ε β} {l : List α} {e : ε}
    (h : ∀ x ∈ l, ∃ y, g x = .ok y) (he : l.mapM g = .error e) : False := by
  obtain ⟨ys, hys⟩ := lmapM_ok' l h
  rw [hys] at he; cases he

/-- `exnTableOpnd` computes for a declared `system_v` integer signature without `context`
items. -/
theorem exnTableOpnd_ok {f : Clif.Function} {et : Clif.ExnTable} {s : Clif.Signature}
    (hs : f.sigDecls.lookup et.sig = some s)
    (hcc : (s.callConv.isNone || s.callConv == some .systemV) = true) (hint : sigIntB s = true)
    (hit : ∀ x ∈ et.items, (match x with | .context _ => false | _ => true) = true) :
    ∃ items, exnTableOpnd f et = .ok (s, items) ∧ items.length = et.items.length := by
  unfold exnTableOpnd
  simp only [hs, hcc, hint, Bool.not_true, Bool.false_eq_true, ite_false, bind, Except.bind]
  split
  · rename_i e he
    refine (lmapM_ne_error (fun x hx => ?_) he).elim
    have := hit x hx
    cases x <;> simp_all [pure, Except.pure]
  · rename_i items hitems
    exact ⟨items, rfl, (Prep.lmapM_ok hitems).1⟩

theorem handlers_length {et : Clif.ExnTable}
    (hit : ∀ x ∈ et.items, (match x with | .context _ => false | _ => true) = true) :
    et.handlers.length = et.items.length := by
  unfold Clif.ExnTable.handlers
  generalize et.items = l at hit
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx := hit x List.mem_cons_self
    have := ih fun y hy => hit y (List.mem_cons_of_mem _ hy)
    cases x <;> simp_all

theorem payloadRegs_length {c : Option Clif.CallConv}
    (h : (c.isNone || c == some .systemV) = true) : (payloadRegs c).length = 2 := by
  rcases c with _ | c
  · rfl
  · cases c <;> simp_all <;> rfl

/-- What the driver needs of a `try_call`'s exception table, from `tryInB`, the values'
registers and `LowerScope.tryRet`. -/
theorem tryOk_of {f : Clif.Function} {ctx : Ctx} {et : Clif.ExnTable} (hin : tryInB f et = true)
    (hval : ∀ td ∈ et.dests, ∀ v, Clif.TryArg.val v ∈ td.args →
      ctx.valueReg? v = some (.vreg v .int))
    (hret : ∀ sig, f.sigDecls.lookup et.sig = some sig → ∀ i, Clif.TryArg.ret i ∈ et.normal.args →
      i < sig.returns.length) :
    ∃ sig items, TryOk f ctx et sig items := by
  unfold tryInB at hin
  cases hs : f.sigDecls.lookup et.sig with
  | none => simp [hs] at hin
  | some s =>
    simp only [hs, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hin
    obtain ⟨⟨⟨⟨⟨⟨⟨hint, hcc⟩, h8⟩, h128⟩, hitems⟩, hhand⟩, hnorm⟩, hnargs⟩ := hin
    obtain ⟨items, hex, hil⟩ := exnTableOpnd_ok hs hcc hint hitems
    have hpl := payloadRegs_length hcc
    refine ⟨s, items, hex, h8, ?_, by rw [hil, handlers_length hitems], fun k td hk => ?_⟩
    · simp only [List.any_eq_false, beq_iff_eq]
      intro x hx; simpa using h128 x hx
    · have htdm : td ∈ et.dests := List.mem_of_getElem? hk
      have hdest : ∀ td : Clif.TryDest, tryDestInB f td = true →
          ∃ tb, f.block? td.block = some tb ∧ tb.params.length = td.args.length := by
        intro td h
        unfold tryDestInB at h
        split at h
        · rename_i tb htb; exact ⟨tb, htb, by simpa using h⟩
        · cases h
      rw [hpl]
      by_cases hkh : k < et.handlers.length
      · have e : td = et.handlers[k] := by
          simp only [Clif.ExnTable.dests] at hk
          rw [List.getElem?_append_left hkh, List.getElem?_eq_getElem hkh] at hk
          exact (Option.some.inj hk).symm
        have hm : td ∈ et.handlers := by rw [e]; exact List.getElem_mem hkh
        obtain ⟨h1, h2⟩ := hhand td hm
        refine ⟨hdest td h1, fun a ha => ?_⟩
        have := h2 a ha
        cases a with
        | val v => exact hval td htdm v ha
        | ret i => simp at this
        | exn i => exact ⟨by omega, by simpa using this⟩
      · have hkl : k < et.dests.length := (List.getElem?_eq_some_iff.mp hk).1
        have hke : k = et.handlers.length := by
          simp only [Clif.ExnTable.dests, List.length_append, List.length_singleton] at hkl
          omega
        have e : td = et.normal := by
          simp only [Clif.ExnTable.dests] at hk
          rw [List.getElem?_append_right (by omega), hke, Nat.sub_self] at hk
          simpa using hk.symm
        subst e
        refine ⟨hdest _ hnorm, fun a ha => ?_⟩
        have := hnargs a ha
        cases a with
        | val v => exact hval _ htdm v ha
        | ret i => exact ⟨hkh, hret s hs i ha⟩
        | exn i => simp at this

/-- The terminator's data computes. -/
theorem dataOk_of {f : Clif.Function} {B : Clif.Block} (hE : Compile.termE B.term = true)
    (ht : termInB f B.term = true) : ∃ data, DataOk f B.term data := by
  have hex : ∀ et, tryInB f et = true → ∃ s items, f.sigDecls.lookup et.sig = some s ∧
      exnTableOpnd f et = .ok (s, items) := by
    intro et h
    unfold tryInB at h
    cases hs : f.sigDecls.lookup et.sig with
    | none => simp [hs] at h
    | some s =>
      simp only [hs, Bool.and_eq_true, List.all_eq_true] at h
      obtain ⟨items, hx, -⟩ := exnTableOpnd_ok hs h.1.1.1.1.1.1.2 h.1.1.1.1.1.1.1 h.1.1.1.2
      exact ⟨s, items, rfl, hx⟩
  unfold DataOk
  cases hb : B.term with
  | tryCall fn args et =>
    rw [hb] at ht
    simp only [termInB, Bool.and_eq_true] at ht
    obtain ⟨s, items, hs, hx⟩ := hex et ht.1
    have h2 := ht.2
    rw [hs] at h2
    split at h2
    · rename_i e s' he hs'
      cases hs'
      simp only [beq_iff_eq] at h2
      simp [tryCallData, hx, he, h2, bind, Except.bind, pure, Except.pure]
    · cases h2
  | tryCallIndirect c args et =>
    rw [hb] at ht
    obtain ⟨s, items, hs, hx⟩ := hex et ht
    simp [tryCallData, hx, bind, Except.bind, pure, Except.pure]
  | returnCall fn args => rw [hb] at hE; cases hE
  | _ => exact ⟨_, rfl⟩

/-- An `sret` signature's `return` has the entry block's `sret` parameter to return. -/
theorem sretBad_false {f : Clif.Function} (hne : f.blocks ≠ []) (hent : Spill.entryParamsB f = true)
    (t : Clif.Terminator) : sretBad f t = false := by
  unfold sretBad
  by_cases hr : (sigRets f.sig != f.sig.returns) = true
  · have hfind : (f.sig.params.find? (·.purpose == .sret)).isSome = true := by
      cases h : f.sig.params.find? (·.purpose == .sret) with
      | none => simp [sigRets, h] at hr
      | some p => rfl
    obtain ⟨x, hx, hp⟩ := List.find?_isSome.mp hfind
    have h2 : (f.sig.params.findIdx? (·.purpose == .sret)).isSome = true := by
      rw [List.findIdx?_isSome]; exact List.any_eq_true.mpr ⟨x, hx, hp⟩
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp h2
    have hil : i < f.sig.params.length := (List.findIdx?_eq_some_iff_getElem.mp hi).1
    obtain ⟨B0, Bs, hbl⟩ := List.exists_cons_of_ne_nil hne
    have hlen : B0.params.length = f.sig.params.length := by
      simp only [Spill.entryParamsB, hbl, beq_iff_eq] at hent; exact hent
    have hsr : (sretRet f).isEmpty = false := by
      simp only [sretRet, hr, ite_true, hbl, List.head?_cons, hi,
        List.getElem?_eq_getElem (show i < B0.params.length by omega)]
      rfl
    simp [hsr]
  · simp only [Bool.not_eq_true] at hr
    simp [hr]

theorem termInB_dests {f : Clif.Function} {t : Clif.Terminator} (h : termInB f t = true) :
    ∀ bc ∈ dests t, (f.block? bc.block).isSome = true := by
  intro bc hbc
  cases t with
  | tryCall fn args et => simp [dests] at hbc
  | tryCallIndirect c args et => simp [dests] at hbc
  | _ => exact List.all_eq_true.mp h bc hbc

theorem termInB_try {f : Clif.Function} {t : Clif.Terminator} {et : Clif.ExnTable}
    (het : IsTryWith t et) (h : termInB f t = true) : tryInB f et = true := by
  rcases het with ⟨fn, args, rfl⟩ | ⟨c, args, rfl⟩
  · simp only [termInB, Bool.and_eq_true] at h; exact h.1
  · exact h

/-! ## The driver is total -/

/-- **Totality of the lowering driver (V7).** On input in scope (subset E, `sigAbiOk`,
dominance, `LowerScope`, branch arity, entry parameters) satisfying `driverInB`, `lowerFunction`
succeeds as soon as the ISLE runs on `buildCtx`'s context make progress (`IselProg`). -/
theorem lowerFunction_ok {f : Clif.Function} (hE : Compile.functionE f = true)
    (hsig : sigAbiOk f.sig = true) (hdom : dominatedB f = true) (hs : lowerScopeB f = true)
    (har : Spill.arityOkB f = true) (hent : Spill.entryParamsB f = true)
    (hin : driverInB f = true)
    (hprog : ∀ ctx ranges st0, buildCtx f = .ok (ctx, ranges, st0) → IselProg f ctx) :
    ∃ vc, lowerFunction f = .ok vc := by
  simp only [driverInB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hin
  obtain ⟨⟨hcc, h8⟩, hbl⟩ := hin
  have hssa : (valueDefs f).Nodup := by
    simp only [dominatedB, Bool.and_eq_true] at hdom; exact nodupB_sound hdom.1
  obtain ⟨ctx, ranges, st0, hb⟩ := buildCtx_ok hE hssa fun B hB s hs => (hbl B hB).1 s hs
  have sp := ctxSpec_of hb
  have hP := hprog _ _ _ hb
  have hd := dominated_of hdom
  have hsc := lowerScope_of hs
  have hreg : ∀ x ∈ valueDefs f, ctx.valueReg? x = some (.vreg x .int) :=
    fun x hx => (sp.facts.vals_int (sp.ctxE hE) x hx).2
  have hE' := hE
  simp only [Compile.functionE, Compile.sigE, Bool.and_eq_true, List.all_eq_true] at hE'
  obtain ⟨⟨⟨⟨hpE, hrE⟩, -⟩, -⟩, hbE⟩ := hE'
  obtain ⟨bytes, hbytes⟩ := sigArgs_ok hsig (List.all_eq_true.mpr hpE)
  obtain ⟨locs, n, hlocs⟩ := sigArgLocs_ok hbytes
  have h2 : (f.sig.returns.any (·.ty == .i128)) = false := by
    simp only [List.any_eq_false, beq_iff_eq]
    intro x hx
    have := hrE x hx
    simp only [Compile.tyE, Bool.and_eq_true, bne_iff_ne] at this
    exact this.2
  have h3 : (f.sig.params.any (·.purpose == .sret) && !f.sig.returns.isEmpty) = false := by
    simp only [sigAbiOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hsig
    rcases hsig.2 with h | h <;> simp [h]
  rw [lowerFunction_eq]
  unfold lowerFunction'
  simp only [hcc, Bool.not_true, Bool.false_eq_true, ite_false, bind, Except.bind, sigParamBytes,
    hbytes, h2, h3, abiRetRegs_returns_int (functionE_sig_int hE).2, retRegs, sigRets_le h8,
    ite_true, Option.isNone_some, hb]
  obtain ⟨dF, hF⟩ := forIn_ok' (blockBody f ctx ranges bytes) f.blocks.zipIdx
    ({ st := st0, alias := #[], nextLabel := f.blocks.length } : DState) (fun x hx d => by
      obtain ⟨B, bi⟩ := x
      have hB : f.blocks[bi]? = some B := List.mem_zipIdx_iff_getElem?.mp hx
      have hBm := List.mem_of_getElem? hB
      have huse := (hd.uses ctx ranges st0 hb bi B hB).2
      have hT := (hbl B hBm).2
      refine blockBody_ok' sp (sp.ctxE hE) hP hB ⟨locs, n, hlocs⟩ (dataOk_of (hbE B hBm).2 hT)
        (sretBad_false hsc.nonempty hent _) (fun bc hbc => ?_) (fun et het => ?_)
        (fun q hq => ⟨_, hreg q.1 ?_⟩) d
      · obtain ⟨tb, htb⟩ := Option.isSome_iff_exists.mp (termInB_dests hT bc hbc)
        exact ⟨tb, htb, Spill.arityOk_of har B hBm bc hbc tb htb, fun a ha =>
          hreg a (availOf_defs (huse a (dests_args_mem hbc ha)))⟩
      · exact tryOk_of (termInB_try het hT)
          (fun td htd v hv => hreg v (availOf_defs (huse v (try_vals_mem het htd hv))))
          (hsc.tryRet B hBm et het)
      · simp only [valueDefs, List.mem_flatMap, List.mem_append, List.mem_map]
        exact ⟨B, hBm, .inl ⟨q, hq, rfl⟩⟩)
  rw [hF]
  exact ⟨_, rfl⟩

/-! ## Non-vacuity -/

/-- `lowerWitnessSrc` (`FV/E2E/LowerDirect.lean`: a loop with block parameters, a back edge
with arguments and a value used after the loop), as a literal. -/
def driverWitness : Clif.Function where
  name := "sum"
  sig := { params := [{ ty := .i64 }], returns := [{ ty := .i64 }] }
  blocks := [
    { id := 0, params := [(0, .i64)], body := [⟨[1], .iconst .i64 0⟩],
      term := .jump ⟨1, [0, 1]⟩ },
    { id := 1, params := [(2, .i64), (3, .i64)],
      body := [⟨[4], .binary .iadd .i64 3 2⟩, ⟨[5], .iconst .i64 1⟩, ⟨[6], .binary .isub .i64 2 5⟩],
      term := .brif 6 ⟨1, [6, 4]⟩ ⟨2, []⟩ },
    { id := 2, term := .ret [4] }]

/-- The callee signature of `driverWitnessTry`. -/
def driverWitnessSig : Clif.Signature where
  params := [{ ty := .i64 }]
  returns := [{ ty := .i64 }]
  callConv := some .systemV

/-- A witness for the statement and `try_call` conditions: a `load` from an `i64` parameter, a
`call` of a declared `system_v` callee, and a `try_call` of it passing the return value to the
normal successor and the exception payload to the handler. -/
def driverWitnessTry : Clif.Function where
  name := "try"
  sig := { params := [{ ty := .i64 }], returns := [{ ty := .i64 }] }
  externs := [(0, { name := "g", sig := driverWitnessSig })]
  sigDecls := [(0, driverWitnessSig)]
  blocks := [
    { id := 0, params := [(0, .i64)],
      body := [⟨[1], .load .load .i64 {} 0 0⟩, ⟨[2], .call 0 [1]⟩],
      term := .tryCall 0 [2]
        { sig := 0, normal := ⟨1, [.ret 0]⟩, items := [.default ⟨2, [.exn 0]⟩] } },
    { id := 1, params := [(3, .i64)], term := .ret [3] },
    { id := 2, params := [(4, .i64)], term := .ret [4] }]

/-- **Non-vacuity of `driverInB`**: it holds, with the other cheap scope conditions of
`lowerFunction_ok`, on the loop witness of `FV/E2E/LowerDirect.lean` and on a `try_call`
witness. -/
theorem driverInB_witness :
    (driverInB driverWitness && Compile.functionE driverWitness && sigAbiOk driverWitness.sig &&
      Spill.arityOkB driverWitness && Spill.entryParamsB driverWitness) = true ∧
    (driverInB driverWitnessTry && Compile.functionE driverWitnessTry &&
      sigAbiOk driverWitnessTry.sig && Spill.arityOkB driverWitnessTry &&
      Spill.entryParamsB driverWitnessTry) = true := by
  decide

end Backend.Proof.Driver
