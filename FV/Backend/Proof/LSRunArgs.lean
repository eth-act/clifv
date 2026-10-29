import FV.Backend.Proof.LSRun
import FV.Backend.Proof.SpillStep4Args

/-!
# The checker accepts the Lean allocator's validated plans (V4b-3, #275): branch arguments

`args_runs`: the last instruction of a block with branch arguments (a `jump` without operands,
`EdgesOk.args`) with the argument copies before it (`Ctx.argMoves`, a sequentialised parallel
copy): its items pass the checker from a `Good` state, and the edge to the only successor (the
checker's parallel copy) gives a state that contains the successor's in-state.

The copy (`seqMoves_runs`) moves every argument of a parameter live at the successor's start into
the parameter's location; the destinations are distinct (two such parameters cover the `jump`'s
post position, `PlanFacts.inter`/`homes`), the scratch register and the temporary are free over
the copy's positions (`regFree_sound`) or the temporary stack slot `nslots` is above every home
(`PlanFacts.homeLt`), so every other vreg live across the `jump` keeps its location. An argument
whose location is not its parameter's is read by an emitted move (`seqMoves_reads`), so its
location is in the frame (`BuildFacts.slots`).
-/

namespace Backend.Proof.LS

open Backend Backend.LinearScan Backend.Proof Backend.Proof.Spill
open Backend.LinearScan.Ctx (Parts blockItems)

/-! ## The argument copy of `Ctx.argMoves` with one successor -/

/-- The moves of `Ctx.argMoves b g` into the parameters of the only successor `t`. -/
private def argMs (c : LinearScan.Ctx) (b t : Nat) : List (Loc × Loc) :=
  ((c.fn.args b).zip (c.fn.params t)).filterMap fun (a, p) =>
    if c.pl.cov p (pos (c.fn.start.getD t 0) 0) then some (c.loc a, c.loc p) else none

/-- The registers the scratch register and the temporary avoid. -/
private def argAvoid (c : LinearScan.Ctx) (b t : Nat) : List Reg :=
  (argMs c b t).flatMap fun (a, p) => [locReg? a, locReg? p].filterMap id

/-- The scratch register of `Ctx.argMoves`. -/
private def argScr (c : LinearScan.Ctx) (b t g : Nat) (cl : RegClass) : Option Reg :=
  scratchReg c.occ [] cl (pos g 0) (pos g 1) (argAvoid c b t)

/-- The temporary of `Ctx.argMoves`. -/
private def argTmp (c : LinearScan.Ctx) (b t g : Nat) (cl : RegClass) : Loc :=
  match scratchReg c.occ [] cl (pos g 0) (pos g 1) ((argScr c b t g cl).toList ++ argAvoid c b t) with
  | some r => .reg r
  | none => .stack c.pl.nslots cl

private theorem argMoves_eq {c : LinearScan.Ctx} {b t g : Nat} {its : List RItem}
    (hs : (c.fn.succs.getD b #[]).toList = [t]) (h : c.argMoves b g = .ok its) :
    seqMoves (argMs c b t) (argScr c b t g) (argTmp c b t g) = .ok its := by
  unfold LinearScan.Ctx.argMoves at h
  rw [hs] at h
  exact h

private theorem mem_argMs {c : LinearScan.Ctx} {b t : Nat} {m : Loc × Loc} (h : m ∈ argMs c b t) :
    ∃ (j a p : Nat), (c.fn.args b)[j]? = some a ∧ (c.fn.params t)[j]? = some p ∧
      c.pl.cov p (pos (c.fn.start.getD t 0) 0) = true ∧ m = (c.loc a, c.loc p) := by
  unfold argMs at h
  obtain ⟨⟨a, p⟩, hx, hf⟩ := List.mem_filterMap.mp h
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hx
  obtain ⟨h1, h2⟩ := List.getElem?_zip_eq_some.mp hj
  dsimp only at hf
  split at hf
  · rename_i hc
    exact ⟨j, a, p, h1, h2, hc, (Option.some.inj hf).symm⟩
  · cases hf

private theorem argMs_mem {c : LinearScan.Ctx} {b t j a p : Nat} (h1 : (c.fn.args b)[j]? = some a)
    (h2 : (c.fn.params t)[j]? = some p) (hc : c.pl.cov p (pos (c.fn.start.getD t 0) 0) = true) :
    (c.loc a, c.loc p) ∈ argMs c b t := by
  unfold argMs
  refine List.mem_filterMap.mpr ⟨(a, p), List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨h1, h2⟩), ?_⟩
  simp only [hc, ↓reduceIte]

private theorem scratchReg_spec {occ : Array (Array LinearScan.Seg)} {taken : List (Reg × Nat × Nat)}
    {cl : RegClass} {s e : Nat} {avoid : List Reg} {r : Reg}
    (h : scratchReg occ taken cl s e avoid = some r) :
    r ∈ scratchOrder cl ∧ r ∉ avoid ∧ regFree occ taken r s e = true := by
  unfold scratchReg at h
  have h2 := List.find?_some h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h2
  refine ⟨List.mem_of_find?_eq_some h, fun hm => ?_, h2.2⟩
  have h3 := h2.1
  rw [List.contains_iff_mem.mpr hm] at h3
  cases h3

private theorem argTmp_cases (c : LinearScan.Ctx) (b t g : Nat) (cl : RegClass) :
    argTmp c b t g cl = .stack c.pl.nslots cl ∨ ∃ r, scratchReg c.occ [] cl (pos g 0) (pos g 1)
      ((argScr c b t g cl).toList ++ argAvoid c b t) = some r ∧ argTmp c b t g cl = .reg r := by
  cases hs : scratchReg c.occ [] cl (pos g 0) (pos g 1) ((argScr c b t g cl).toList ++ argAvoid c b t) with
  | none => exact .inl (by unfold argTmp; rw [hs])
  | some r => exact .inr ⟨r, rfl, by unfold argTmp; rw [hs]⟩

/-- The temporary is of its class and is not the scratch register. -/
private theorem argTmp_cls (c : LinearScan.Ctx) (b t g : Nat) (cl : RegClass) :
    LocCls (argTmp c b t g cl) cl ∧ ∀ r, argScr c b t g cl = some r → argTmp c b t g cl ≠ .reg r := by
  rcases argTmp_cases c b t g cl with he | ⟨r, hr, he⟩ <;> rw [he]
  · exact ⟨.inr ⟨_, rfl⟩, fun r _ h => by cases h⟩
  · obtain ⟨h1, h2, -⟩ := scratchReg_spec hr
    obtain ⟨ha, hc, -⟩ := scratchOrder_ok h1
    refine ⟨.inl ⟨r, rfl, ha, hc⟩, fun r' hr' h => ?_⟩
    injection h with h
    subst h
    exact h2 (List.mem_append_left _ (by rw [hr']; simp))

private theorem argScr_cls {c : LinearScan.Ctx} {b t g : Nat} {cl : RegClass} {r : Reg}
    (h : argScr c b t g cl = some r) : LocCls (.reg r) cl := by
  obtain ⟨ha, hc, -⟩ := scratchOrder_ok (scratchReg_spec h).1
  exact .inl ⟨r, rfl, ha, hc⟩

/-! ## Helpers -/

private theorem loc_ne_save (c : LinearScan.Ctx) (v : Nat) (r : Reg) : c.loc v ≠ .save r := by
  unfold LinearScan.Ctx.loc Fn.loc
  split <;> intro h <;> cases h

/-- Two vregs of one location never cover one position. -/
private theorem loc_inj {vc : VCode} {c : LinearScan.Ctx} (hpf : PlanFacts vc c) {v w q : Nat}
    (hv : v < c.fn.nv) (hw : w < c.fn.nv) (he : c.loc v = c.loc w) (hcv : c.pl.cov v q = true)
    (hcw : c.pl.cov w q = true) : v = w := by
  unfold LinearScan.Ctx.loc Fn.loc at he
  revert he
  cases hrv : c.pl.regOf v with
  | some r =>
    cases hrw : c.pl.regOf w with
    | some r' =>
      intro he
      simp only [Loc.reg.injEq] at he
      subst he
      exact hpf.inter v w r q hrv hrw hcv hcw
    | none => intro he; cases he
  | none =>
    cases hrw : c.pl.regOf w with
    | some r' => intro he; cases he
    | none =>
      intro he
      simp only [Loc.stack.injEq] at he
      exact hpf.homes v w q hv hw hrv hrw he.1 he.2 hcv hcw

private theorem idxOf?_of_nodup {l : List Nat} (hnd : l.Nodup) {j x : Nat} (h : l[j]? = some x) :
    l.idxOf? x = some j := by
  obtain ⟨hj, he⟩ := List.getElem?_eq_some_iff.mp h
  refine List.idxOf?_eq_some_iff.mpr ⟨hj, he, fun j' hj' he' => ?_⟩
  exact List.pairwise_iff_getElem.mp hnd j' j (by omega) hj hj' (he'.trans he.symm)

private theorem getElem?_of_idxOf? {l : List Nat} {x j : Nat} (h : l.idxOf? x = some j) :
    l[j]? = some x := by
  obtain ⟨hj, he, -⟩ := List.idxOf?_eq_some_iff.mp h
  exact List.getElem?_eq_some_iff.mpr ⟨hj, he⟩

private theorem vregs_filterMap : ∀ (l : List Reg), (∀ r ∈ l, ∃ n c, r = .vreg n c) →
    l.filterMap LinearScan.vregOf = l.map Reg.homeNum
  | [], _ => rfl
  | r :: l, h => by
    obtain ⟨n, c, rfl⟩ := h r List.mem_cons_self
    rw [List.filterMap_cons, List.map_cons, vregs_filterMap l (fun r hr => h r (.tail _ hr))]
    rfl

private theorem getElem?_homeNum {l : List Reg} {j x : Nat} (h : (l.map Reg.homeNum)[j]? = some x) :
    ∃ r, l[j]? = some r ∧ r.homeNum = x := by
  rw [List.getElem?_map] at h
  cases hr : l[j]? with
  | none => rw [hr] at h; cases h
  | some r => rw [hr] at h; exact ⟨r, rfl, Option.some.inj h⟩

/-- A parameter of `t` live at its start: its argument is live at the `jump` `g`, the parameter
from the copy on. -/
private theorem edge_param {vc : VCode} {c : LinearScan.Ctx} (hpf : PlanFacts vc c) {b t g : Nat}
    (ht : t < vc.blocks.size) (hb : b ∈ (c.fn.preds.getD t #[]).toList) (hgl : c.lastOf b = g)
    {v kk : Nat} (hv : v < c.fn.nv) (hc : c.pl.cov v (pos (c.fn.start.getD t 0) 0) = true)
    (hk : (c.fn.params t).idxOf? v = some kk) :
    ∃ a, (c.fn.args b)[kk]? = some a ∧ c.pl.cov a (pos g 0) = true ∧
      c.pl.covI v (pos g 1) (pos g 4) = true := by
  have h := hpf.edge v hv t ht hc b hb
  simp only [LinearScan.Ctx.edgeOk, hgl, hk, Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  revert h
  cases ha : (c.fn.args b)[kk]? with
  | none => intro h; cases h
  | some a =>
    intro h
    simp only [Bool.and_eq_true] at h
    exact ⟨a, rfl, h.1, h.2⟩

/-- Another vreg live at the start of `t` is live after the `jump` `g`. -/
private theorem edge_other {vc : VCode} {c : LinearScan.Ctx} (hpf : PlanFacts vc c) {b t g : Nat}
    (ht : t < vc.blocks.size) (hb : b ∈ (c.fn.preds.getD t #[]).toList) (hgl : c.lastOf b = g)
    {v : Nat} (hv : v < c.fn.nv) (hc : c.pl.cov v (pos (c.fn.start.getD t 0) 0) = true)
    (hk : (c.fn.params t).idxOf? v = none) : c.pl.cov v (pos g 4) = true := by
  have h := hpf.edge v hv t ht hc b hb
  simpa only [LinearScan.Ctx.edgeOk, hgl, hk] using h

/-- No birth inside the `jump` of a vreg that is no parameter of its successor. -/
private theorem nobirth_last {vc : VCode} {c : LinearScan.Ctx} (hf : FnOk vc c.fn) {b : Nat}
    {vb : VBlock} (hvb : vc.blocks[b]? = some vb) {k : Nat} {i : MInst}
    (hi : vb.insts[k]? = some i) (hops : i.operands = .ok #[]) {t : Nat}
    (hs : (c.fn.succs.getD b #[]).toList = [t]) {v : Nat} (hv : v ∉ c.fn.params t) :
    ∀ s, pos (c.fn.start.getD b 0 + k) 0 < s → s ≤ pos (c.fn.start.getD b 0 + k) 4 →
      c.birthOk v s = false := by
  have hk : k < vb.insts.size := (Array.getElem?_eq_some_iff.mp hi).1
  intro s h1 h2
  rw [Bool.eq_false_iff]
  intro hb
  obtain ⟨sl, hsl, rfl⟩ : ∃ sl, sl < 5 ∧ s = pos (c.fn.start.getD b 0 + k) sl :=
    ⟨s - 5 * (c.fn.start.getD b 0 + k), by unfold pos at *; omega, by unfold pos at *; omega⟩
  obtain ⟨-, hb1, hb2⟩ := birthOk_pos hsl hb
  have hsl0 : sl ≠ 0 := by unfold pos at h1; omega
  by_cases hsl1 : sl = 1
  · subst hsl1
    have := hb1 rfl
    simp only [Fn.paramAt, hf.blkGetD hvb hk, hs, Bool.and_eq_true, List.contains_iff_mem] at this
    exact hv this.2
  · obtain ⟨o, ho, -⟩ := hb2 hsl0 hsl1
    rw [(hf.opsGetD hvb hi hops).2.1] at ho
    simp at ho

section
variable {vc : VCode} {c : LinearScan.Ctx} {rf : RFunc} {D : Nat → Nat → Bool}
  (H : Hyps vc c rf D)
include H

/-- A register free over `[s, e]` is not the location of a vreg live there. -/
private theorem free_ne {taken : List (Reg × Nat × Nat)} {r : Reg} {s e : Nat}
    (h : regFree c.occ taken r s e = true) {v q : Nat} (hq1 : s ≤ q) (hq2 : q ≤ e)
    (hc : c.pl.cov v q = true) : c.loc v ≠ .reg r := by
  intro he
  have := (regFree_sound H.plan H.occ h).1 v (loc_reg he) q hq1 hq2 hc
  cases this

/-- The temporary is not the location of a vreg live during the copy. -/
private theorem tmp_ne {b t g v q : Nat} (hv : v < c.fn.nv) (hq1 : pos g 0 ≤ q) (hq2 : q ≤ pos g 1)
    (hc : c.pl.cov v q = true) (cl : RegClass) : argTmp c b t g cl ≠ c.loc v := by
  rcases argTmp_cases c b t g cl with he | ⟨r, hr, he⟩ <;> rw [he]
  · intro he'
    unfold LinearScan.Ctx.loc Fn.loc at he'
    revert he'
    cases hr : c.pl.regOf v with
    | some r => intro he'; cases he'
    | none =>
      intro he'
      simp only [Loc.stack.injEq] at he'
      have h1 := he'.1
      have := H.plan.homeLt v hv hr q hc
      omega
  · exact (free_ne H (scratchReg_spec hr).2.2 hq1 hq2 hc).symm

/-- **The last instruction of a block with branch arguments** (a `jump` without operands): the
argument copies and the `jump` feed the successor's in-state. -/
theorem args_runs {b : Nat} {vb : VBlock} (hvb : vc.blocks[b]? = some vb) {p : Parts}
    (hp : c.blockParts b = .ok p) {k : Nat} {args : List RItem} {io : IOut}
    (hk : p.insts[k]? = some (args, io)) (hlast : k + 1 = vb.insts.size)
    (hba : vb.branchArgs ≠ #[]) {A : Nat → Bool}
    (hA : A = availAt vb.insts (availStart vc c.fn.succs c.fn.preds D b) k) {a : AState}
    (hg : Good c rf A (pos (c.fn.start.getD b 0 + k) 0) a) :
    Runs (ctxOf vc c rf) vb k (args ++ io.pre.map LinearScan.mv ++
      (if vb.insts[k]? matches some (.rets _) then restoresOf rf.saved else []) ++
        [.op k io.allocs] ++ io.post.map LinearScan.mv) a
      fun k' a' => k' = k + 1 ∧ ∀ s ∈ ((ctxOf vc c rf).succs[b]?.getD #[]).toList,
        ∃ e, (ctxOf vc c rf).edge b s a' = .ok e ∧ (inState vc c rf D s).le e = true := by
  have hf := H.fn
  have hpf := H.plan
  have hE := H.loc.2.2 _ _ hf.cfg
  obtain ⟨⟨i, hT, hops⟩, t, tb, hss, htb, hsz, hcls, hnd⟩ := hE.args b vb hvb hba
  obtain ⟨-, hi⟩ := back_get hT
  rw [show vb.insts.size - 1 = k by omega] at hi
  have hkn : k ≠ vb.insts.size := by omega
  obtain ⟨hgo, -, hgi⟩ := hf.opsGetD hvb hi hops
  -- not a `Rets`: it has a successor
  have hnr : ∀ us, i ≠ .rets us := by
    intro us he
    obtain ⟨t', ts, ht', -, hts, hlen, -⟩ := (Prep.cfg_spec hf.cfg).blk b vb hvb
    rw [hT] at ht'
    cases ht'
    rw [hss] at hts
    cases hts
    subst he
    simp [MInst.targets] at hlen
  have hsl : (c.fn.succs.getD b #[]).toList = [t] := by
    rw [Array.getD_eq_getD_getElem?, hss]; rfl
  have hstart := hf.startSucc hvb
  have hgl : c.lastOf b = c.fn.start.getD b 0 + k := by
    unfold LinearScan.Ctx.lastOf; omega
  obtain ⟨hio, hargs0, -⟩ := (partsFacts hp).inst k args io hk
  have hseq := argMoves_eq hsl (hargs0 (by omega))
  have hpiece : ∀ it ∈ args, it ∈ blockItems vb p [] := (piece_mem (L := []) hk).1
  -- the `jump`'s own items: no moves, no restores
  obtain ⟨ops', hops', hok, -⟩ := H.loc.1 b vb k i hvb hi
  rw [hops] at hops'
  cases hops'
  have hIF := H.inst _ i #[] io hgi hgo hok (by simp) hio
  have hpre : io.pre = [] := by
    cases h : io.pre with
    | nil => rfl
    | cons m l =>
      obtain ⟨j, o, hj, -⟩ := hIF.pre m (by rw [h]; exact List.mem_cons_self)
      simp at hj
  have hpost : io.post = [] := by
    cases h : io.post with
    | nil => rfl
    | cons m l =>
      obtain ⟨j, o, hj, -⟩ := hIF.post m (by rw [h]; exact List.mem_cons_self)
      simp at hj
  rw [hpre, hpost, hi]
  split
  · rename_i h
    exact absurd (Option.some.inj h) (hnr _)
  simp only [List.map_nil, List.append_nil, Bool.false_eq_true, ↓reduceIte]
  -- the CFG and the parameters
  generalize hgdef : c.fn.start.getD b 0 + k = g at hg hgl hgo hgi hIF hseq
  have ht : t < vc.blocks.size := (Array.getElem?_eq_some_iff.mp htb).1
  have hbp : b ∈ (c.fn.preds.getD t #[]).toList := mem_preds hf.cfg hss (by simp)
  have hpv : ∀ r ∈ tb.params.toList, ∃ n c, r = .vreg n c := fun r hr =>
    let ⟨n, c', h, _⟩ := hf.nv_regs t tb htb r (List.mem_append_left _ hr); ⟨n, c', h⟩
  have hxv : ∀ r ∈ vb.branchArgs.toList, ∃ n c, r = .vreg n c := fun r hr =>
    let ⟨n, c', h, _⟩ := hf.nv_regs b vb hvb r (List.mem_append_right _ hr); ⟨n, c', h⟩
  have hpsEq : c.fn.params t = tb.params.toList.map Reg.homeNum := by
    rw [hf.params htb, vregs_filterMap _ hpv]
  have hxsEq : c.fn.args b = vb.branchArgs.toList.map Reg.homeNum := by
    rw [hf.args hvb, vregs_filterMap _ hxv]
  have hndp : (c.fn.params t).Nodup := hpsEq ▸ hnd
  have hpnv : ∀ q ∈ c.fn.params t, q < c.fn.nv := by
    intro q hq
    rw [hpsEq] at hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    obtain ⟨n, c', rfl, hn⟩ := hf.nv_regs t tb htb r (List.mem_append_left _ hr)
    exact hn
  have hanv : ∀ x ∈ c.fn.args b, x < c.fn.nv := by
    intro x hx
    rw [hxsEq] at hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    obtain ⟨n, c', rfl, hn⟩ := hf.nv_regs b vb hvb r (List.mem_append_right _ hr)
    exact hn
  have hcl : ∀ (bb : Nat) (vbb : VBlock), vc.blocks[bb]? = some vbb → ∀ (n : Nat) (cl : RegClass),
      Reg.vreg n cl ∈ vbb.params.toList ++ vbb.branchArgs.toList → c.fn.clsOf n = cl := by
    intro bb vbb hbb n cl hm
    obtain ⟨n', c', he, hc⟩ := H.loc.2.1.2 bb vbb hbb _ hm
    cases he
    exact hf.cls n cl hc
  have hclsj : ∀ (j x q : Nat), (c.fn.args b)[j]? = some x → (c.fn.params t)[j]? = some q →
      c.fn.clsOf x = c.fn.clsOf q := by
    intro j x q hx hq
    rw [hxsEq] at hx
    rw [hpsEq] at hq
    obtain ⟨ar, har, rfl⟩ := getElem?_homeNum hx
    obtain ⟨pr, hpr, rfl⟩ := getElem?_homeNum hq
    have hmar := List.mem_of_getElem? har
    have hmpr := List.mem_of_getElem? hpr
    rw [Array.getElem?_toList] at har hpr
    obtain ⟨x, y, cl, rfl, rfl⟩ := hcls j ar pr har hpr
    show c.fn.clsOf x = c.fn.clsOf y
    rw [hcl b vb hvb x cl (List.mem_append_right _ hmar), hcl t tb htb y cl (List.mem_append_left _ hmpr)]
  -- the moves
  have hmv : ∀ m ∈ argMs c b t, ∃ (j x q : Nat), (c.fn.args b)[j]? = some x ∧ (c.fn.params t)[j]? = some q ∧
      x < c.fn.nv ∧ q < c.fn.nv ∧ c.pl.cov x (pos g 0) = true ∧
      c.pl.covI q (pos g 1) (pos g 4) = true ∧ m = (c.loc x, c.loc q) := by
    intro m hm
    obtain ⟨j, x, q, hjx, hjq, hc, rfl⟩ := mem_argMs hm
    have hq := hpnv q (List.mem_of_getElem? hjq)
    obtain ⟨x', hjx', hcx, hcq⟩ := edge_param hpf ht hbp hgl hq hc (idxOf?_of_nodup hndp hjq)
    rw [hjx] at hjx'
    cases hjx'
    exact ⟨j, x, q, hjx, hjq, hanv x (List.mem_of_getElem? hjx), hq, hcx, hcq, rfl⟩
  have hdst : ∀ m ∈ argMs c b t, ∀ m' ∈ argMs c b t, m.2 = m'.2 → m.1 = m'.1 := by
    intro m hm m' hm' he
    obtain ⟨j, x, q, hjx, hjq, -, hq, -, hcq, rfl⟩ := hmv m hm
    obtain ⟨j', x', q', hjx', hjq', -, hq', -, hcq', rfl⟩ := hmv m' hm'
    have hqq : q = q' := loc_inj hpf hq hq' he
      (cov_of_covI hcq (by unfold pos; omega) (Nat.le_refl _))
      (cov_of_covI hcq' (by unfold pos; omega) (Nat.le_refl _))
    subst hqq
    have hjj := (idxOf?_of_nodup hndp hjq).symm.trans (idxOf?_of_nodup hndp hjq')
    cases hjj
    rw [hjx] at hjx'
    cases hjx'
    rfl
  have hms : ∀ m ∈ argMs c b t, ∃ cl, LocCls m.1 cl ∧ LocCls m.2 cl := by
    intro m hm
    obtain ⟨j, x, q, hjx, hjq, -, -, -, -, rfl⟩ := hmv m hm
    exact ⟨_, loc_cls hpf (hclsj j x q hjx hjq), loc_cls hpf rfl⟩
  have hscr : ∀ (cl : RegClass) (r : Reg), argScr c b t g cl = some r → LocCls (.reg r) cl ∧
      ∀ m ∈ argMs c b t, m.1 ≠ .reg r ∧ m.2 ≠ .reg r := by
    intro cl r hr
    refine ⟨argScr_cls hr, fun m hm => ?_⟩
    obtain ⟨j, x, q, -, -, -, -, hcx, hcq, rfl⟩ := hmv m hm
    have hfr := (scratchReg_spec hr).2.2
    exact ⟨free_ne H hfr (Nat.le_refl _) (by unfold pos; omega) hcx,
      free_ne H hfr (by unfold pos; omega) (Nat.le_refl _)
        (cov_of_covI hcq (Nat.le_refl _) (by unfold pos; omega))⟩
  have htmp : ∀ cl, LocCls (argTmp c b t g cl) cl ∧
      (∀ m ∈ argMs c b t, m.1 ≠ argTmp c b t g cl ∧ m.2 ≠ argTmp c b t g cl) ∧
      ∀ r, argScr c b t g cl = some r → argTmp c b t g cl ≠ .reg r := by
    intro cl
    refine ⟨(argTmp_cls c b t g cl).1, fun m hm => ?_, (argTmp_cls c b t g cl).2⟩
    obtain ⟨j, x, q, -, -, hx, hq, hcx, hcq, rfl⟩ := hmv m hm
    exact ⟨(tmp_ne H hx (Nat.le_refl _) (by unfold pos; omega) hcx cl).symm,
      (tmp_ne H hq (by unfold pos; omega) (Nat.le_refl _)
        (cov_of_covI hcq (Nat.le_refl _) (by unfold pos; omega)) cl).symm⟩
  have hslots : ∀ it ∈ args, ∀ l ∈ it.locs, ∀ s cl, l = .stack s cl → s < rf.spillSlots :=
    fun it hit => H.build.slots b vb p hvb hp it (hpiece it hit)
  refine Runs.append (seqMoves_runs (cc := ctxOf vc c rf) hkn hseq hg.size hslots hdst hms hscr htmp)
    fun k1 a1 ⟨e1, _, get1, fr1, wr1⟩ => ?_
  subst e1
  have nw : ∀ l, (∀ m ∈ argMs c b t, m.2 ≠ l) → (∀ cl, argTmp c b t g cl ≠ l) →
      (∀ cl r, argScr c b t g cl = some r → l ≠ .reg r) → a1.get l = a.get l := by
    intro l h1 h2 h3
    refine fr1 l fun it hit s he => ?_
    rcases wr1 it hit s l he with ⟨m, hm, hml⟩ | ⟨cl, hcl⟩ | ⟨cl, r, hr, hrl⟩
    · exact h1 m hm hml
    · exact h2 cl hcl
    · exact h3 cl r hr hrl
  -- a vreg live across the `jump` that is no parameter keeps its location
  have keepv : ∀ v, v < c.fn.nv → c.pl.covI v (pos g 0) (pos g 4) = true → v ∉ c.fn.params t →
      a1.get (c.loc v) = a.get (c.loc v) := by
    intro v hv hcv hvp
    have hc0 := cov_of_covI hcv (Nat.le_refl _) (by unfold pos; omega)
    refine nw _ (fun m hm hml => ?_) (fun cl => tmp_ne H hv (Nat.le_refl _) (by unfold pos; omega) hc0 cl)
      (fun cl r hr => free_ne H (scratchReg_spec hr).2.2 (Nat.le_refl _) (by unfold pos; omega) hc0)
    obtain ⟨j, x, q, -, hjq, -, hq, -, hcq, rfl⟩ := hmv m hm
    have := loc_inj hpf hq hv hml (cov_of_covI hcq (by unfold pos; omega) (Nat.le_refl _))
      (cov_of_covI hcv (by unfold pos; omega) (Nat.le_refl _))
    subst this
    exact hvp (List.mem_of_getElem? hjq)
  -- the `jump`
  have hnil : ((#[] : Array Operand).zip io.allocs).toList = [] := by simp
  refine Runs.op hkn hi hops (stepOp_of (hIF.static _ _) (fun q hq => by rw [hnil] at hq; cases hq)
    (by rw [hnil]; rfl) (retCheck_other hnr _)) ⟨rfl, ?_⟩
  rw [hnil]
  have keep2 : ∀ l x, (∀ r ∈ i.clobbers, Loc.reg r ≠ l) → x ∈ a1.get l → x ∈ (transferOp i [] a1).get l :=
    fun l x hc hx => transferOp_keep (fun y hy => by cases hy) hc hx (fun y hy => by cases hy)
  have noclob : ∀ v, c.pl.cov v (pos g 3) = true → ∀ r ∈ i.clobbers, Loc.reg r ≠ c.loc v := by
    intro v hc r hr he
    have := hpf.clob g i hgi r hr v (loc_reg he.symm)
    rw [hc] at this
    cases this
  -- the edge
  intro s hs
  have hs' : s = t := by
    simp only [ctxOf, hss, Option.getD_some] at hs
    simpa using hs
  subst hs'
  have hs0 : s ≠ 0 := fun h => preds_empty hf.cfg (h ▸ hE.entry.2.1) hss (by simp)
  have hnd0 : i.normalDead = none := by
    unfold MInst.normalDead
    split
    · exact absurd (hE.tryEdge b vb _ _ #[s] s hvb hT).1 hba
    · rfl
  have hF : (ctxOf vc c rf).edgeForget b s (transferOp i [] a1) = transferOp i [] a1 := by
    rcases edgeForget_cases (vc := vc) (c := ctxOf vc c rf) rfl hvb hT hops (transferOp i [] a1)
      with h | ⟨jn, n, h, -⟩
    · exact h
    · rw [hnd0] at h; cases h
  have hie : vb.branchArgs.isEmpty = false := by
    rw [Bool.eq_false_iff]; intro h; exact hba (Array.isEmpty_iff.mp h)
  have hC : (ctxOf vc c rf).edgeCopy b s (transferOp i [] a1) =
      .ok ((transferOp i [] a1).parCopy (c.fn.params s) (c.fn.args b)) := by
    rw [hpsEq, hxsEq]
    unfold CheckCtx.edgeCopy
    rw [show (ctxOf vc c rf).vc = vc from rfl, hvb, htb]
    simp only [ensure_true (b := vb.branchArgs.size == tb.params.size) (by simp [hsz]), hie,
      mapM_vregNum _ hpv, mapM_vregNum _ hxv, ensure_true (b := decide _) (decide_eq_true hnd),
      bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte]
  refine ⟨_, by unfold CheckCtx.edge; rw [hF]; exact hC, le_of_mem fun l x hx => ?_⟩
  obtain ⟨hlv, hx⟩ := mem_inState hx
  rcases hx with ⟨v, rfl, hv, hcv, hD, hel⟩ | ⟨r, rfl, hr⟩
  · -- a vreg live at the successor's start
    have hep : entryPairs vc c.fn.succs c.fn.preds s = [] := by
      cases h : entryPairs vc c.fn.succs c.fn.preds s with
      | nil => rfl
      | cons y l =>
        have hy : y ∈ entryPairs vc c.fn.succs c.fn.preds s := by rw [h]; exact List.mem_cons_self
        obtain ⟨p', vbp, ssp, j, hp', hvbp, hssp, hj, hyt⟩ := entryPairs_spec hy
        obtain ⟨rfl, -⟩ := preds_single hf.cfg hss (j := 0) (by simp) hp'
        rw [hvb] at hvbp
        cases hvbp
        obtain ⟨T', ops', hT', -, hops', hyk, -⟩ := termEdgeDefs_spec hyt
        rw [hT] at hT'
        cases hT'
        rw [hops] at hops'
        cases hops'
        have := (mem_keptPairs hyk).1
        simp at this
    rw [entryLoc_none (fun y hy => by rw [hep] at hy; cases hy)] at hel
    subst hel
    have hDv : D s v = true := by
      rw [entryStored_eq, hep] at hD
      simpa using hD
    have hea := H.avail.edges _ _ hf.cfg b vb #[s] s tb hvb hss (by simp) htb v hDv
    have hAe : availAt vb.insts (availStart vc c.fn.succs c.fn.preds D b) vb.insts.size = A := by
      rw [hA]
      funext w
      rw [← hlast, availAt_succ hi, availInst_eq hops]
      simp [isDefOf]
    rw [hAe] at hea
    unfold edgeAvail at hea
    rw [← hpsEq] at hea
    cases hidx : (c.fn.params s).idxOf? v with
    | none =>
      rw [hidx] at hea
      have hvp : v ∉ c.fn.params s := List.idxOf?_eq_none_iff.mp hidx
      have h4 := edge_other hpf ht hbp hgl hv hcv hidx
      have hI := covI_of_nobirth hpf hv h4 (by unfold pos; omega)
        (hgdef ▸ nobirth_last hf hvb hi hops hsl hvp)
      have h0 := hg.vregs v hv (cov_of_covI hI (Nat.le_refl _) (by unfold pos; omega)) hea hlv
      rw [← keepv v hv hI hvp] at h0
      have h2 := keep2 _ _ (noclob v (cov_of_covI hI (by unfold pos; omega) (by unfold pos; omega))) h0
      exact mem_parCopy_keep h2 fun q hq he => by
        injection he with he
        subst he
        exact hvp hq
    | some kk =>
      have hjp := getElem?_of_idxOf? hidx
      obtain ⟨x, hjx, hcx, hcI⟩ := edge_param hpf ht hbp hgl hv hcv hidx
      have hAx : A x = true := by
        rw [hidx] at hea
        simp only at hea
        split at hea
        · rename_i ar har
          have : ar.homeNum = x := by
            rw [hxsEq, List.getElem?_map, Array.getElem?_toList, har] at hjx
            exact Option.some.inj hjx
          rw [← this]
          exact hea
        · cases hea
      have hm : (c.loc x, c.loc v) ∈ argMs c b s := argMs_mem hjx hjp hcv
      have hxl : LocValid rf (c.loc x) := by
        by_cases heq : c.loc x = c.loc v
        · rw [heq]; exact hlv
        · obtain ⟨it, hit, hl⟩ := seqMoves_reads hseq _ hm heq
          exact locValid_of_cls (loc_cls hpf (cl := c.fn.clsOf x) rfl)
            fun s' c' he => hslots it hit _ hl s' c' he
      have h0 := hg.vregs x (hanv x (List.mem_of_getElem? hjx)) hcx hAx hxl
      have h1 : Sym.vreg x ∈ a1.get (c.loc v) := by
        have := get1 _ hm
        simp only at this
        rw [this]
        exact h0
      have h2 := keep2 _ _ (noclob v (cov_of_covI hcI (by unfold pos; omega) (by unfold pos; omega))) h1
      exact mem_parCopy_add (List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨hjp, hjx⟩)) h2
  · -- a callee-saved register's entry value
    rcases hr with ⟨rfl, hrc, hr0⟩ | ⟨rfl, -, hrs⟩
    · have hrs : r ∉ rf.saved := hr0.resolve_left hs0
      have h0 := (hg.callee r hrc).2 hrs
      have h1 : Sym.entry r ∈ a1.get (.reg r) := by
        rw [fr1 (.reg r) fun it hit s' he =>
          H.build.notSaved r hrc hrs b vb p hvb hp it (hpiece it hit) (by rw [he]; simp [RItem.locs])]
        exact h0
      exact mem_parCopy_keep (transferOp_entry h1 fun y hy => by cases hy) fun q _ he => by cases he
    · have hrc := H.build.saved r hrs
      have h0 := (hg.callee r hrc).1 hrs
      have h1 : Sym.entry r ∈ a1.get (.save r) := by
        rw [nw (.save r) (fun m hm hml => by
            obtain ⟨j, x, q, -, -, -, -, -, -, rfl⟩ := hmv m hm
            exact loc_ne_save c q r hml)
          (fun cl he => by
            rcases argTmp_cases c b s g cl with h | ⟨r', -, h⟩ <;> rw [h] at he <;> cases he)
          (fun cl r' _ he => by cases he)]
        exact h0
      exact mem_parCopy_keep (keep2 _ _ (fun r' _ he => by cases he) h1) fun q _ he => by cases he

end

end Backend.Proof.LS
