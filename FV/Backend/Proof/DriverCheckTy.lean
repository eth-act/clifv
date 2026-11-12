import FV.Backend.Proof.LowerLoopCtxT

/-!
# The typed driver model and validator (S11e5 Stage C, slice 2)

`LowerShape`/`lowerCheck` describe `lowerFunction`'s VCode with integer value registers
(`.vreg x .int`): result copies (`extraOf`), the entry's `Args` pairs and stack-argument loads
(`entryRegOf`, `entryLoadOf`: an integer `ldr`), block parameters, branch arguments and a
`try_call`'s normal-return arguments (`normArgReg`). `lowerFunction` itself is class-aware
(S11e3): it uses `ctx.valueReg? x`, which on a float-capable context is `vregOf ctx x =
.vreg x (valClassOf ctx x)` (`CtxInvT.typedReg`), and loads a stack-passed parameter with
`stackArgLoad` (`ldr s`/`ldr d` into a float vreg).

This file is the typed model beside the integer one: `extraOfT`, `entryRegOfT`, `entryLoadOfT`,
`preT`, `segT`, `normArgRegT`, `succOkT`, `blockOkT`, `shapeOkT` (with `ctxOkT` and the
supported-instruction check `instScopeOk`), `entryOkBT` (register parameters in x0..x8 or
v0..v7), `lowerCheckT`; `LowerShapeT` (`LowerShape` with `CtxInvT` + `InstScopeT` and the typed
model). Soundness: `lowerShapeT_of_ok`, `loweringT_of_check` and the tail facts.

Integer equivalence: on an integer context (`CtxE`) the typed model is the integer one
(`extraOfT_int`, `preT_int`, `segT_int`, `normArgRegT_int`, `succOkT_int`, `blockOkT_int`);
`lowerShapeT_of_lowerShape`, `lowerShape_of_lowerShapeT` (with `CtxInv`), and the integer
validator's acceptance implies the typed one's (`lowerCheckT_of_lowerCheck`). The integer
theorems (`ctxOk_sound`, `lowerShape_of_ok`, `lowering_of_check`) are unchanged.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-! ## The typed model -/

/-- The vreg of value `x` in a float-capable context: `vreg x` of its type's class (what
`ctx.valueReg? x` is for a typed value, `CtxInvT.typedReg`). -/
def vregOf (ctx : Ctx) (x : Nat) : Reg := .vreg x (valClassOf ctx x)

/-- `lowerFunction`'s `mov` for a result the rules returned in a real register, into the
result's vreg of its class. -/
def extraOfT (ctx : Ctx) (results : List Nat) (rss : List (List Reg)) : List MInst :=
  (results.zip rss).filterMap fun (r, rs) => match rs with
    | [.vreg ..] => none
    | [out] => some (.mov .size64 (vregOf ctx r) out)
    | _ => none

/-- The register of a `try_call`'s normal-return argument: a value's vreg of its class, a
return's vreg, `xzr` for a payload. -/
def normArgRegT (ctx : Ctx) (R : Reg → Reg) (rets : List Reg) : Clif.TryArg → Reg
  | .val v => R (vregOf ctx v)
  | .ret i => R (rets.getD i .xzr)
  | .exn _ => .xzr

section
variable (f : Clif.Function) (vc : VCode) (ctx : Ctx) (st0 : LState) (R : Reg → Reg)
  (gn : Nat → Nat) (bl : List BLow)

/-- The VCode segment of statement `j` of block `bi` (typed result copies). -/
def segT (bi j : Nat) : List MInst :=
  match f.blocks[bi]?, bl[bi]? with
  | some B, some L =>
    match B.body[j]?, L.sl[j]? with
    | some stm, some sl => (sl.st'.emitted.toList ++ extraOfT ctx stm.results sl.rss).map (·.mapRegs R)
    | _, _ => []
  | _, _ => []

/-- The `Args` pair of a register-passed parameter, its vreg of its class. -/
def entryRegOfT (q : ((Clif.ValueId × Clif.Ty) × ArgLoc) × Nat) : Option (Reg × Reg) :=
  match q.1.2 with
  | .reg p => some (R (vregOf ctx q.1.1.1), p)
  | .stack _ => none

/-- The load of a stack-passed parameter (`stackArgLoad`: `ldr`/`ldrb`/`ldrh` into an integer
vreg, `ldr s`/`ldr d` into a float one). -/
def entryLoadOfT (q : ((Clif.ValueId × Clif.Ty) × ArgLoc) × Nat) : Option MInst :=
  match q.1.2 with
  | .stack off => some (stackArgLoad (R (vregOf ctx q.1.1.1)) q.2 (.fpOffset (16 + off)))
  | .reg _ => none

def entryRegsT (B : Clif.Block) : List (Reg × Reg) := (entryParams f B).filterMap (entryRegOfT ctx R)

def entryLoadsT (B : Clif.Block) : List MInst := (entryParams f B).filterMap (entryLoadOfT ctx R)

/-- The entry block's code before its statements (typed `gen_arg_setup`). -/
def preT (bi : Nat) : List MInst :=
  match bi, f.blocks[bi]? with
  | 0, some B => .args (entryRegsT f ctx R B) :: entryLoadsT f ctx R B
  | _, _ => []

/-- Index in block `bi` where statement `j`'s segment starts (typed model). -/
def posT (bi j : Nat) : Nat :=
  (preT f ctx R bi).length + ((List.range j).map fun j' => (segT f ctx R bl bi j').length).sum

end

/-- The successor facts of `LowerShapeT` (`succOk` with typed branch/normal-return
arguments). -/
def succOkT (f : Clif.Function) (vc : VCode) (ctx : Ctx) (R : Reg → Reg) (B : Clif.Block)
    (L : BLow) : Bool :=
  match B.term with
  | .jump bc => match blockIdx? f bc.block with
    | some tl => decide (L.targets = [tl])
    | none => false
  | .tryCall _ _ et | .tryCallIndirect _ _ et => decide (L.targets.length = et.dests.length) &&
    match blockIdx? f et.normal.block, L.targets.getLast?, L.tl with
    | some tl, some tlab, some T => match vc.blocks[tlab]? with
      | some eb => decide (eb.insts = #[.jump tl]) && decide (eb.params = #[]) &&
          decide (eb.branchArgs = (et.normal.args.map (normArgRegT ctx R T.regs.1)).toArray) &&
          et.normal.args.all fun
            | .val _ => true
            | .ret i => decide (i < T.sig.returns.length)
            | .exn _ => false
      | none => false
    | _, _, _ => false
  | t => decide (L.targets.length = (dests t).length) &&
    ((dests t).zip L.targets).all fun (bc, tlab) => match blockIdx? f bc.block with
      | none => false
      | some tl =>
        if bc.args = [] then decide (tlab = tl) else
        match vc.blocks[tlab]? with
        | some eb => decide (eb.insts = #[.jump tl]) && decide (eb.params = #[]) &&
            decide (eb.branchArgs = (bc.args.map fun a => R (vregOf ctx a)).toArray)
        | none => false

/-- The per-block facts of `LowerShapeT`. -/
def blockOkT (f : Clif.Function) (vc : VCode) (ctx : Ctx) (st0 : LState) (R : Reg → Reg)
    (gn : Nat → Nat) (bl : List BLow) (bi : Nat) (B : Clif.Block) (L : BLow) : Bool :=
  match vc.blocks[bi]? with
  | none => false
  | some vb =>
    decide (L.sl.length = B.body.length) &&
    (List.range B.body.length).all (fun j => match B.body[j]?, L.sl[j]? with
      | some stm, some sl => stmtOk ctx st0 gn (L.start + j) stm sl
      | _, _ => false) &&
    L.tst.emitted.isEmpty && decide (st0.nextVreg ≤ L.tst.nextVreg) &&
    decide (vb.insts.toList = preT f ctx R bi ++
      ((List.range B.body.length).map (segT f ctx R bl bi)).flatten ++ tseg R bl bi) &&
    !(tseg R bl bi).isEmpty &&
    decide (vb.params = (if bi = 0 then #[] else (B.params.map fun p => vregOf ctx p.1).toArray)) &&
    decide (vb.branchArgs = (match B.term with
      | .jump bc => (bc.args.map fun a => R (vregOf ctx a)).toArray
      | _ => #[])) &&
    succOkT f vc ctx R B L &&
    (match ctx.insts[L.start + B.body.length]? with
      | some info => info.data == .op .unit && info.results.isEmpty && info.resTys.isEmpty &&
          info.clif.isNone
      | none => false)

/-- `LowerShapeT f vc ctx st0 (renOf gn) gn bl`, decided. -/
def shapeOkT (f : Clif.Function) (vc : VCode) (ctx : Ctx) (st0 : LState) (gn : Nat → Nat)
    (bl : List BLow) : Bool :=
  (ctxOkT f ctx && instScopeOk ctx) && decide (ctx.valReg.size ≤ st0.nextVreg) &&
  f.blocks.all (fun B => B.params.all fun p => decide (gn p.1 = p.1)) &&
  decide (bl.length = f.blocks.length) && decide (f.blocks.length ≤ vc.blocks.size) &&
  (List.range vc.blocks.size).all (fun l => match vc.blocks[l]? with
    | some vb => decide (vb.label = l)
    | none => true) &&
  ((List.range f.blocks.length).all fun bi => match f.blocks[bi]?, bl[bi]? with
    | some B, some L => blockOkT f vc ctx st0 (renOf gn) gn bl bi B L
    | _, _ => false) &&
  decide (st0.nextVreg ≤ f.freshValue)

/-- The signature's parameter locations and byte sizes compute, one per parameter, and the
register-passed parameters are in x0..x8 or v0..v7 (`entryOkB` with float registers). -/
def entryOkBT (f : Clif.Function) : Bool :=
  (locsOf f.sig).length == f.sig.params.length &&
    (locsOf f.sig).all (fun l => match l with
      | .reg (.x n) => decide (n ≤ 8)
      | .reg (.v n) => decide (n ≤ 7)
      | .reg _ => false
      | .stack _ => true) &&
    match sigParamBytes f.sig with
    | .ok _ => true
    | .error _ => false

/-- **The typed lowering validator** (`lowerCheck` with `shapeOkT` and `entryOkBT`). -/
def lowerCheckT (f : Clif.Function) (vc : VCode) : Bool :=
  match buildCtx f with
  | .error _ => false
  | .ok (ctx, _, st0) =>
    match lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
        f.blocks.length with
    | none => false
    | some bl =>
      let gn := gnAt (gnTable st0.nextVreg (aliasOf f bl))
      shapeOkT f vc ctx st0 gn bl && certOk f ctx st0 gn bl (inFix f ctx gn) && brIdxOk f ctx &&
        ((f.blocks.any (·.term.isTry) || !vc.hasTryCall) && (hasTls f || !vc.hasTls)) &&
        (callsStackOkB f vc.outgoing && entryOkBT f)

/-! ## `LowerShapeT` -/

section
variable (f : Clif.Function) (vc : VCode) (ctx : Ctx) (st0 : LState) (R : Reg → Reg)
  (gn : Nat → Nat) (bl : List BLow)

/-- **The structure of `lowerFunction f`'s VCode, typed** (`LowerShape` over a float-capable
context: `CtxInvT` and the supported instructions `InstScopeT` in place of `CtxInv`, and the
typed model's entry code, result copies, block parameters and edge arguments). -/
structure LowerShapeT : Prop where
  hctx : ∃ ranges, buildCtx f = .ok (ctx, ranges, st0)
  ctxInvT : CtxInvT f ctx
  scope : InstScopeT ctx
  ren : VRenaming R gn
  temps : ∀ n, st0.nextVreg ≤ n → gn n = n
  params : ∀ B ∈ f.blocks, ∀ p ∈ B.params, gn p.1 = p.1
  len : bl.length = f.blocks.length
  size : f.blocks.length ≤ vc.blocks.size
  valsBelow : ∀ x r, ctx.valueReg? x = some r → x < st0.nextVreg
  labels : ∀ l (vb : VBlock), vc.blocks[l]? = some vb → vb.label = l
  fresh : st0.nextVreg ≤ f.freshValue
  tslot : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B → bl[bi]? = some L →
    ctx.insts[L.start + B.body.length]? = some (⟨.op .unit, [], [], none⟩ : IInfo)
  blk : ∀ bi B L, f.blocks[bi]? = some B → bl[bi]? = some L →
    ∃ vb, vc.blocks[bi]? = some vb ∧
    L.sl.length = B.body.length ∧
    (∀ j stm sl, B.body[j]? = some stm → L.sl[j]? = some sl →
      (∃ info, ctx.insts[L.start + j]? = some info ∧ info.clif = some stm.inst ∧
        info.results = stm.results) ∧
      sl.st.emitted = #[] ∧ st0.nextVreg ≤ sl.st.nextVreg ∧
      (∃ tr, runTerm ctx "lower" [.inst (L.start + j)] sl.st = .ok (some (.regsVec sl.rss), sl.st', tr)) ∧
      (∀ (k : Nat) r out cls, stm.results[k]? = some r → sl.rss[k]? = some [.vreg out cls] →
        gn r = gn out)) ∧
    L.tst.emitted = #[] ∧ st0.nextVreg ≤ L.tst.nextVreg ∧
    (B.term.isTry = false → L.tl = none ∧ termData (abiTerm f B.term) = .ok L.data ∧
      ∃ out tr, runTerm (termCtx ctx (L.start + B.body.length) L.data)
        (termCall B.term (L.start + B.body.length) L.targets).1
        (termCall B.term (L.start + B.body.length) L.targets).2 L.tst = .ok (some out, L.tst', tr)) ∧
    (∀ et, IsTryWith B.term et → ∃ T, L.tl = some T ∧
      tryCallData f B.term = .ok L.data ∧ exnTableOpnd f et = .ok (T.sig, T.items) ∧
      tryRegsOf T.sig L.tst = some (T.regs, T.st1) ∧ tryInfoOf T.sig T.items L.targets = some T.info ∧
      ∃ out tr, runTerm (tryCtx ctx (L.start + B.body.length) L.data T.regs) "lower_branch"
        [.inst (L.start + B.body.length), .labels L.targets] { T.st1 with emitted := #[] } =
        .ok (some out, L.tst', tr)) ∧
    vb.insts.toList = preT f ctx R bi ++ ((List.range B.body.length).map (segT f ctx R bl bi)).flatten ++
      tseg R bl bi ∧
    tseg R bl bi ≠ [] ∧
    vb.params = (if bi = 0 then #[] else (B.params.map fun p => vregOf ctx p.1).toArray) ∧
    vb.branchArgs = (match B.term with
      | .jump bc => (bc.args.map fun a => R (vregOf ctx a)).toArray
      | _ => #[]) ∧
    (match B.term with
      | .jump bc => ∃ tl, blockIdx? f bc.block = some tl ∧ L.targets = [tl]
      | .tryCall _ _ et | .tryCallIndirect _ _ et => L.targets.length = et.dests.length ∧
        ∃ tl tlab T eb, blockIdx? f et.normal.block = some tl ∧ L.targets.getLast? = some tlab ∧
          L.tl = some T ∧ vc.blocks[tlab]? = some eb ∧ eb.insts = #[.jump tl] ∧ eb.params = #[] ∧
          eb.branchArgs = (et.normal.args.map (normArgRegT ctx R T.regs.1)).toArray ∧
          ∀ a ∈ et.normal.args, match a with
            | .val _ => True
            | .ret i => i < T.sig.returns.length
            | .exn _ => False
      | _ => L.targets.length = (dests B.term).length ∧
        ∀ (k : Nat) bc tlab, (dests B.term)[k]? = some bc → L.targets[k]? = some tlab →
          ∃ tl, blockIdx? f bc.block = some tl ∧
            (bc.args = [] → tlab = tl) ∧
            (bc.args ≠ [] → ∃ eb, vc.blocks[tlab]? = some eb ∧ eb.insts = #[.jump tl] ∧
              eb.params = #[] ∧ eb.branchArgs = (bc.args.map fun a => R (vregOf ctx a)).toArray))

end

/-! ## Soundness -/

theorem succOkT_sound {f : Clif.Function} {vc : VCode} {ctx : Ctx} {R : Reg → Reg}
    {B : Clif.Block} {L : BLow} (h : succOkT f vc ctx R B L = true) :
    match B.term with
    | .jump bc => ∃ tl, blockIdx? f bc.block = some tl ∧ L.targets = [tl]
    | .tryCall _ _ et | .tryCallIndirect _ _ et => L.targets.length = et.dests.length ∧
      ∃ tl tlab T eb, blockIdx? f et.normal.block = some tl ∧ L.targets.getLast? = some tlab ∧
        L.tl = some T ∧ vc.blocks[tlab]? = some eb ∧ eb.insts = #[.jump tl] ∧ eb.params = #[] ∧
        eb.branchArgs = (et.normal.args.map (normArgRegT ctx R T.regs.1)).toArray ∧
        ∀ a ∈ et.normal.args, match a with
          | .val _ => True
          | .ret i => i < T.sig.returns.length
          | .exn _ => False
    | _ => L.targets.length = (dests B.term).length ∧
      ∀ (k : Nat) bc tlab, (dests B.term)[k]? = some bc → L.targets[k]? = some tlab →
        ∃ tl, blockIdx? f bc.block = some tl ∧
          (bc.args = [] → tlab = tl) ∧
          (bc.args ≠ [] → ∃ eb, vc.blocks[tlab]? = some eb ∧ eb.insts = #[.jump tl] ∧
            eb.params = #[] ∧ eb.branchArgs = (bc.args.map fun a => R (vregOf ctx a)).toArray) := by
  have gen : ∀ t : Clif.Terminator, (decide (L.targets.length = (dests t).length) &&
      ((dests t).zip L.targets).all fun (bc, tlab) => match blockIdx? f bc.block with
        | none => false
        | some tl =>
          if bc.args = [] then decide (tlab = tl) else
          match vc.blocks[tlab]? with
          | some eb => decide (eb.insts = #[.jump tl]) && decide (eb.params = #[]) &&
              decide (eb.branchArgs = (bc.args.map fun a => R (vregOf ctx a)).toArray)
          | none => false) = true →
      L.targets.length = (dests t).length ∧
      ∀ (k : Nat) bc tlab, (dests t)[k]? = some bc → L.targets[k]? = some tlab →
        ∃ tl, blockIdx? f bc.block = some tl ∧
          (bc.args = [] → tlab = tl) ∧
          (bc.args ≠ [] → ∃ eb, vc.blocks[tlab]? = some eb ∧ eb.insts = #[.jump tl] ∧
            eb.params = #[] ∧ eb.branchArgs = (bc.args.map fun a => R (vregOf ctx a)).toArray) := by
    intro t h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨h.1, fun k bc tlab hbc htl => ?_⟩
    have hz : ((dests t).zip L.targets)[k]? = some (bc, tlab) := by
      rw [List.getElem?_zip_eq_some]; exact ⟨hbc, htl⟩
    have := List.all_eq_true.mp h.2 _ (List.mem_of_getElem? hz)
    simp only at this
    split at this
    · cases this
    · rename_i tl htlb
      refine ⟨tl, htlb, fun ha => ?_, fun ha => ?_⟩
      · simpa [ha] using this
      · simp only [ha, ite_false] at this
        split at this
        · rename_i eb heb
          simp only [Bool.and_eq_true, decide_eq_true_eq] at this
          exact ⟨eb, heb, this.1.1, this.1.2, this.2⟩
        · cases this
  have htry : ∀ et : Clif.ExnTable, (decide (L.targets.length = et.dests.length) &&
      match blockIdx? f et.normal.block, L.targets.getLast?, L.tl with
      | some tl, some tlab, some T => match vc.blocks[tlab]? with
        | some eb => decide (eb.insts = #[.jump tl]) && decide (eb.params = #[]) &&
            decide (eb.branchArgs = (et.normal.args.map (normArgRegT ctx R T.regs.1)).toArray) &&
            et.normal.args.all fun
              | .val _ => true
              | .ret i => decide (i < T.sig.returns.length)
              | .exn _ => false
        | none => false
      | _, _, _ => false) = true →
      L.targets.length = et.dests.length ∧
      ∃ tl tlab T eb, blockIdx? f et.normal.block = some tl ∧ L.targets.getLast? = some tlab ∧
        L.tl = some T ∧ vc.blocks[tlab]? = some eb ∧ eb.insts = #[.jump tl] ∧ eb.params = #[] ∧
        eb.branchArgs = (et.normal.args.map (normArgRegT ctx R T.regs.1)).toArray ∧
        ∀ a ∈ et.normal.args, match a with
          | .val _ => True
          | .ret i => i < T.sig.returns.length
          | .exn _ => False := by
    intro et h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hlen, h⟩ := h
    refine ⟨hlen, ?_⟩
    split at h
    · rename_i tl tlab T htl htlab hT
      split at h
      · rename_i eb heb
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        refine ⟨tl, tlab, T, eb, htl, htlab, hT, heb, h.1.1.1, h.1.1.2, h.1.2, fun a ha => ?_⟩
        have := List.all_eq_true.mp h.2 a ha
        cases a <;> simp_all
      · cases h
    · cases h
  unfold succOkT at h
  split at h
  · rename_i bc hj
    try rw [hj]
    split at h
    · rename_i tl htl
      exact ⟨tl, htl, by simpa using h⟩
    · cases h
  · rename_i fn args et hj
    try rw [hj]
    exact htry et h
  · rename_i c args et hj
    try rw [hj]
    exact htry et h
  · first
    | exact gen _ h
    | (rename_i hnj hnt hnti
       have := gen B.term h
       split
       · rename_i bc hj; exact absurd hj (hnj bc)
       · rename_i fn args et hj; exact absurd hj (hnt fn args et)
       · rename_i c args et hj; exact absurd hj (hnti c args et)
       · exact this)

/-- **Soundness of the typed shape check.** -/
theorem lowerShapeT_of_ok {f : Clif.Function} {vc : VCode} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : LState} {bl : List BLow} {gn : Nat → Nat}
    (hb : buildCtx f = .ok (ctx, ranges, st0))
    (hl : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
      f.blocks.length = some bl)
    (hgn : ∀ n, st0.nextVreg ≤ n → gn n = n) (hs : shapeOkT f vc ctx st0 gn bl = true) :
    LowerShapeT f vc ctx st0 (renOf gn) gn bl := by
  obtain ⟨-, hlb⟩ := lowBlocks_spec hl
  simp only [shapeOkT, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hctx, hsc⟩, hvb⟩, hpar⟩, hlen⟩, hsize⟩, hlab⟩, hblk⟩, hfresh⟩ := hs
  have hblk' : ∀ bi B L, f.blocks[bi]? = some B → bl[bi]? = some L →
      blockOkT f vc ctx st0 (renOf gn) gn bl bi B L = true := by
    intro bi B L hB hL
    have := all_range hblk (lt_of_getElem? hB)
    simpa [hB, hL] using this
  refine ⟨⟨ranges, hb⟩, ctxOkT_sound hctx, instScopeOk_sound hsc, renOf_vrenaming gn, hgn, ?_,
    hlen, hsize, ?_, ?_, hfresh, ?_, ?_⟩
  · intro B hB p hp
    have := List.all_eq_true.mp (List.all_eq_true.mp hpar B hB) p hp
    simpa using this
  · intro x r hx
    have : x < ctx.valReg.size := lt_valReg hx
    omega
  · intro l vb hvb
    have := all_range hlab (Array.getElem?_eq_some_iff.mp hvb).1
    simpa [hvb] using this
  · intro bi B L hB hL
    have h := hblk' bi B L hB hL
    unfold blockOkT at h
    split at h
    · cases h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have h' := h.2
      split at h'
      · rename_i info hinfo
        simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff, Option.isNone_iff_eq_none] at h'
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h'
        rw [hinfo]
        cases info
        simp_all
      · cases h'
  · intro bi B L hB hL
    obtain ⟨hsl, hsj, htemp0, nl0, nl', hterm⟩ := hlb bi B L hB hL
    obtain ⟨hnt, hty⟩ := lowTerm_spec hterm
    have h := hblk' bi B L hB hL
    unfold blockOkT at h
    split at h
    · cases h
    · rename_i vb hvb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hst⟩, htemp⟩, hle⟩, hcode⟩, htne⟩, hpars⟩, hbargs⟩, hsucc⟩, -⟩ := h
      refine ⟨vb, hvb, hsl, ?_, by simpa using htemp, hle, fun hnt' => ?_, fun et ht => ?_,
        hcode, by simpa using htne, hpars, hbargs, succOkT_sound hsucc⟩
      rotate_left
      · obtain ⟨h1, h2, out, tr, h3⟩ := hnt hnt'
        exact ⟨h1, h2, out, tr, h3⟩
      · obtain ⟨T, h1, h2, h3, -, h5, h6, out, tr, h7⟩ := hty et ht
        exact ⟨T, h1, h2, h3, h5, h6, out, tr, h7⟩
      intro j stm sl hj hslj
      have := all_range hst (lt_of_getElem? hj)
      rw [hj, hslj] at this
      obtain ⟨h1, h2, h3, h4⟩ := stmtOk_sound this
      exact ⟨h1, h2, h3, hsj j sl hslj, h4⟩

/-- **Soundness of the typed lowering validator**: `lowerCheckT f vc = true` gives the typed
structure of the VCode, an SSA availability certificate and the `br_table` index typing. -/
theorem loweringT_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheckT f vc = true) :
    ∃ ctx st0 R gn bl A, LowerShapeT f vc ctx st0 R gn bl ∧ Cert f ctx st0 gn bl A ∧
      ∀ B ∈ f.blocks, BrIdxTyped ctx B.term := by
  unfold lowerCheckT at h
  split at h
  · cases h
  · rename_i ctx ranges st0 hb
    split at h
    · cases h
    · rename_i bl hl
      simp only [Bool.and_eq_true] at h
      have hS := lowerShapeT_of_ok (gn := gnAt (gnTable st0.nextVreg (aliasOf f bl))) hb hl
        (fun n hn => gnAt_temp hn) h.1.1.1.1
      exact ⟨ctx, st0, _, _, bl, _, hS, cert_of_ok hS.len h.1.1.1.2, brIdx_of_ok h.1.1.2⟩

/-- The tail of `lowerCheckT` (its conjuncts after the shape and certificate). -/
theorem lowerCheckT_tail {f : Clif.Function} {vc : VCode} (h : lowerCheckT f vc = true) :
    ((f.blocks.any (·.term.isTry) || !vc.hasTryCall) && (hasTls f || !vc.hasTls)) = true ∧
      callsStackOkB f vc.outgoing = true ∧ entryOkBT f = true := by
  unfold lowerCheckT at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [Bool.and_eq_true] at h
      exact ⟨by simp only [Bool.and_eq_true]; exact h.1.2, h.2.1, h.2.2⟩

/-- A function without `try_call` lowers to VCode without `tryCall` (`lowerCheckT`). -/
theorem noTryCallT_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheckT f vc = true)
    (hf : ∀ B ∈ f.blocks, B.term.isTry = false) : vc.hasTryCall = false := by
  have h1 := (lowerCheckT_tail h).1
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h1
  rcases h1.1 with h2 | h2
  · obtain ⟨B, hB, hB'⟩ := List.any_eq_true.mp h2
    rw [hf B hB] at hB'; cases hB'
  · exact h2

/-- A function without `tls_value` lowers to VCode without `ElfTlsGetAddr` (`lowerCheckT`). -/
theorem noTlsT_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheckT f vc = true)
    (hf : hasTls f = false) : vc.hasTls = false := by
  have h1 := (lowerCheckT_tail h).1
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h1
  rcases h1.2 with h2 | h2
  · rw [hf] at h2; cases h2
  · exact h2

/-- The calls of `f` fit the VCode's outgoing area (`lowerCheckT`). -/
theorem callsStackT_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheckT f vc = true) :
    CallsStack f vc.outgoing := by
  have h2 := (lowerCheckT_tail h).2.1
  simp only [callsStackOkB, Bool.and_eq_true] at h2
  intro B hB st hst fn args e hi he
  have := List.all_eq_true.mp (List.all_eq_true.mp h2.1.1 B hB) st hst
  rw [hi] at this
  simp only [he, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

/-- The callees of the `try_call`s of `f` fit the VCode's outgoing area (`lowerCheckT`). -/
theorem tryStackT_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheckT f vc = true) :
    TryStack f vc.outgoing := by
  have h2 := (lowerCheckT_tail h).2.1
  simp only [callsStackOkB, Bool.and_eq_true] at h2
  intro B hB fn args et hi e he
  have := List.all_eq_true.mp h2.1.2 B hB
  rw [hi] at this
  simp only [he, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

/-- The call-site signatures of the indirect calls of `f` fit the VCode's outgoing area
(`lowerCheckT`, S5). -/
theorem indStackT_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheckT f vc = true) :
    IndStack (indSigs f) vc.outgoing := by
  have h2 := (lowerCheckT_tail h).2.1
  simp only [callsStackOkB, Bool.and_eq_true] at h2
  intro s hs
  have := List.all_eq_true.mp h2.2 s hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

/-- The entry's parameter locations and byte sizes compute (`lowerCheckT`'s `entryOkBT`). -/
theorem entryOkT_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheckT f vc = true) :
    (locsOf f.sig).length = f.sig.params.length ∧ ∃ bytes, sigParamBytes f.sig = .ok bytes := by
  have h2 := (lowerCheckT_tail h).2.2
  simp only [entryOkBT, Bool.and_eq_true, beq_iff_eq] at h2
  refine ⟨h2.1.1, ?_⟩
  have h3 := h2.2
  split at h3
  · exact ⟨_, ‹_›⟩
  · cases h3

/-- The register-passed parameters of the entry are in x0..x8 or v0..v7 (`entryOkBT`). -/
theorem entryRegsT_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheckT f vc = true) :
    ∀ l ∈ locsOf f.sig, ∀ r, l = .reg r → (∃ n, r = .x n ∧ n ≤ 8) ∨ (∃ n, r = .v n ∧ n ≤ 7) := by
  have h2 := (lowerCheckT_tail h).2.2
  simp only [entryOkBT, Bool.and_eq_true, beq_iff_eq] at h2
  intro l hl r hr
  have := List.all_eq_true.mp h2.1.2 l hl
  subst hr
  cases r with
  | x n => exact .inl ⟨n, rfl, by simpa using this⟩
  | v n => exact .inr ⟨n, rfl, by simpa using this⟩
  | _ => cases this

/-! ## Integer equivalence -/

section
variable {ctx : Ctx} (hE : CtxE ctx)
include hE

/-- On an integer context every value's class is `int`. -/
theorem valClassOf_int (x : Nat) : valClassOf ctx x = .int := by
  unfold valClassOf
  cases ht : ctx.valueType? x with
  | none => rfl
  | some t => simp only [Option.map_some, Option.getD_some, valClass_of_eCTys (hE x t ht)]

theorem vregOf_int (x : Nat) : vregOf ctx x = .vreg x .int := by
  rw [vregOf, valClassOf_int hE]

theorem extraOfT_int (results : List Nat) (rss : List (List Reg)) :
    extraOfT ctx results rss = extraOf results rss := by
  simp only [extraOfT, extraOf, vregOf_int hE] <;> rfl

theorem normArgRegT_int (R : Reg → Reg) (rets : List Reg) :
    normArgRegT ctx R rets = normArgReg R rets := by
  funext a; cases a <;> simp [normArgRegT, normArgReg, vregOf_int hE]

theorem segT_int (f : Clif.Function) (R : Reg → Reg) (bl : List BLow) (bi j : Nat) :
    segT f ctx R bl bi j = seg f R bl bi j := by
  simp only [segT, seg, extraOfT_int hE] <;> rfl

theorem entryRegOfT_int (R : Reg → Reg) : entryRegOfT ctx R = entryRegOf R := by
  funext q; simp only [entryRegOfT, entryRegOf, vregOf_int hE] <;> rfl

theorem entryLoadOfT_int {R : Reg → Reg} {gn : Nat → Nat} (hR : VRenaming R gn) :
    entryLoadOfT ctx R = entryLoadOf R := by
  funext q
  obtain ⟨⟨⟨v, ty⟩, loc⟩, b⟩ := q
  cases loc <;> simp [entryLoadOfT, entryLoadOf, stackArgLoad, hR.vreg, Reg.homeCls, vregOf_int hE]

theorem preT_int (f : Clif.Function) {R : Reg → Reg} {gn : Nat → Nat} (hR : VRenaming R gn)
    (bi : Nat) : preT f ctx R bi = pre f R bi := by
  simp only [preT, pre, entryRegsT, entryLoadsT, entryRegs, entryLoads, entryRegOfT_int hE,
    entryLoadOfT_int hE hR] <;> rfl

theorem succOkT_int (f : Clif.Function) (vc : VCode) (R : Reg → Reg) (B : Clif.Block) (L : BLow) :
    succOkT f vc ctx R B L = succOk f vc R B L := by
  simp only [succOkT, succOk, vregOf_int hE, normArgRegT_int hE] <;> rfl

theorem blockOkT_int (f : Clif.Function) (vc : VCode) (st0 : LState) {R : Reg → Reg}
    {gn : Nat → Nat} (hR : VRenaming R gn) (bl : List BLow) (bi : Nat) (B : Clif.Block)
    (L : BLow) : blockOkT f vc ctx st0 R gn bl bi B L = blockOk f vc ctx st0 R gn bl bi B L := by
  have hs : segT f ctx R bl bi = seg f R bl bi := funext (segT_int hE f R bl bi)
  simp only [blockOkT, blockOk, preT_int hE f hR, vregOf_int hE, succOkT_int hE, hs] <;> rfl

end

/-- **Integer specialization of the typed shape**: an integer shape is a typed one. -/
theorem lowerShapeT_of_lowerShape {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} (h : LowerShape f vc ctx st0 R gn bl) :
    LowerShapeT f vc ctx st0 R gn bl := by
  have hE : CtxE ctx := h.ctxInv.valTyE
  refine ⟨h.hctx, h.ctxInv.toT, h.ctxInv.instScopeT, h.ren, h.temps, h.params, h.len, h.size,
    h.valsBelow, h.labels, h.fresh, h.tslot, fun bi B L hB hL => ?_⟩
  obtain ⟨vb, hvb, hsl, hst, hte, htn, hnt, hty, hcode, htne, hpar, hba, hsucc⟩ := h.blk bi B L hB hL
  refine ⟨vb, hvb, hsl, hst, hte, htn, hnt, hty, ?_, htne, ?_, ?_, ?_⟩
  · rw [hcode, preT_int hE f h.ren, show segT f ctx R bl bi = seg f R bl bi from
      funext (segT_int hE f R bl bi)]
  · rw [hpar]; simp only [vregOf_int hE]
  · simp only [vregOf_int hE]; exact hba
  · simp only [vregOf_int hE, normArgRegT_int hE]; exact hsucc

/-- **The typed shape over an integer context is the integer shape.** -/
theorem lowerShape_of_lowerShapeT {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} (h : LowerShapeT f vc ctx st0 R gn bl)
    (hI : CtxInv f ctx) : LowerShape f vc ctx st0 R gn bl := by
  have hE : CtxE ctx := hI.valTyE
  refine ⟨h.hctx, hI, h.ren, h.temps, h.params, h.len, h.size, h.valsBelow, h.labels, h.fresh,
    h.tslot, fun bi B L hB hL => ?_⟩
  obtain ⟨vb, hvb, hsl, hst, hte, htn, hnt, hty, hcode, htne, hpar, hba, hsucc⟩ := h.blk bi B L hB hL
  refine ⟨vb, hvb, hsl, hst, hte, htn, hnt, hty, ?_, htne, ?_, ?_, ?_⟩
  · rw [hcode, preT_int hE f h.ren, show segT f ctx R bl bi = seg f R bl bi from
      funext (segT_int hE f R bl bi)]
  · rw [hpar]; simp only [vregOf_int hE]
  · simp only [vregOf_int hE] at hba; exact hba
  · simp only [vregOf_int hE, normArgRegT_int hE] at hsucc; exact hsucc

/-- The integer shape check implies the typed one. -/
theorem shapeOkT_of_shapeOk {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {gn : Nat → Nat} {bl : List BLow} (h : shapeOk f vc ctx st0 gn bl = true) :
    shapeOkT f vc ctx st0 gn bl = true := by
  simp only [shapeOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hctx, hvb⟩, hpar⟩, hlen⟩, hsize⟩, hlab⟩, hblk⟩, hfresh⟩ := h
  have hI := ctxOk_sound hctx
  have hE : CtxE ctx := hI.valTyE
  simp only [shapeOkT, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨ctxOkT_complete hI.toT, instScopeOk_complete hI.instScopeT⟩, hvb⟩, hpar⟩,
    hlen⟩, hsize⟩, hlab⟩, ?_⟩, hfresh⟩
  refine List.all_eq_true.mpr fun bi hbi => ?_
  have := List.all_eq_true.mp hblk bi hbi
  split
  · rw [blockOkT_int hE f vc st0 (renOf_vrenaming gn)]
    simpa [*] using this
  · simp_all

/-- `entryOkB` implies `entryOkBT`. -/
theorem entryOkBT_of_entryOkB {f : Clif.Function} (h : entryOkB f = true) : entryOkBT f = true := by
  simp only [entryOkB, entryOkBT, Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨⟨h.1.1, fun l hl => ?_⟩, h.2⟩
  have := h.1.2 l hl
  split <;> simp_all

/-- **The integer validator's acceptance implies the typed one's.** -/
theorem lowerCheckT_of_lowerCheck {f : Clif.Function} {vc : VCode} (h : lowerCheck f vc = true) :
    lowerCheckT f vc = true := by
  unfold lowerCheck at h
  unfold lowerCheckT
  split at h
  · cases h
  · rename_i ctx ranges st0 hb
    rw [hb]
    split at h
    · cases h
    · rename_i bl hl
      simp only [hl, Bool.and_eq_true] at h ⊢
      exact ⟨⟨⟨⟨shapeOkT_of_shapeOk h.1.1.1.1, h.1.1.1.2⟩, h.1.1.2⟩, h.1.2⟩,
        h.2.1, entryOkBT_of_entryOkB h.2.2⟩

end Backend.Proof.Driver
