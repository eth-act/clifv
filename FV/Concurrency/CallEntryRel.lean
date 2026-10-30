import FV.Concurrency.CallSegGeo
import FV.Concurrency.CallSegCall

/-!
# The callee's entry memory relation (#473, `SegOkG` call case, item (1))

At a caller's paused `call`, the CLIF callee is entered by `Clif.enterFunc` on the caller's
memory `cm`. With the slot-placement oracle at the caller's body `sp` (`cm.place = some
⟨spv x :: sps, fr, none⟩`, no slot-byte oracle) and the oracle's frame of the callee its compiled
frame drop and slot offsets (`slotOffs`), the callee's slots are placed in its Arm frame below
the caller's body `sp`:

* `enterSlots_at`: the placed slots, allocations, bytes and the oracle after `enterSlots`;
* **`callee_relW`**: the callee's CLIF entry memory is related (`RelW`, with the callee's world
  `RL.F` and slot base) to its body-entry world `bodyOf FB.af (enter FB x)`, given the caller's
  `MemRel` at the call (with its world `RA.F`) and its `StRel` (`Q`'s state relation): the
  caller's valid bytes are outside `RA.F`, so outside the callee's `RL.F` (`Nested.privA_sub`),
  hold the same bytes in `x` (`SameWorld`), and the callee's slots lie in its slot area, outside
  its `RL.F` (`Chain.slot_not_F`), uninitialised.
-/

namespace Concurrency.CallEntryRel

open Arm ArmThread Prog Backend Backend.Proof E2E FrameDisj ArmAllocThread LinkedMachine
  LinkedMachine.Link CallSegCall CallSegGeo

/-- **The oracle's slot offsets of a compiled function**: its slot base plus the CLIF layout. -/
def slotOffs (af : AFunc) (f : Clif.Function) : Clif.SlotId → Nat :=
  fun id => af.slotBase + ((slotLayout f.slots).1.lookup id).getD 0

/-- **`enterSlots` with the oracle at `c`** (no slot-byte oracle): the slots placed at
`c - d + off`, allocated uninitialised, the oracle at `c - d`. -/
theorem enterSlots_at {f : Clif.Function} {mem : Clif.Mem} {c : BitVec 64}
    {sps : List (BitVec 64)} {fr : String → Option (Nat × (Clif.SlotId → Nat))} {d : Nat}
    {off : Clif.SlotId → Nat} (hp : mem.place = some ⟨c :: sps, fr, none⟩)
    (hf : fr f.name = some (d, off)) :
    (Clif.enterSlots f mem).1 =
        f.slots.map (fun p => (p.1, (c - BitVec.ofNat 64 d).toNat + off p.1)) ∧
      (Clif.enterSlots f mem).2.symbols = mem.symbols ∧
      (∀ x ∈ (Clif.enterSlots f mem).2.allocs, x ∈ mem.allocs ∨
        ∃ p ∈ f.slots, x = ⟨(c - BitVec.ofNat 64 d).toNat + off p.1, p.2.size, false⟩) ∧
      (∀ a b, (Clif.enterSlots f mem).2.bytes a = some b → mem.bytes a = some b ∧
        ∀ p ∈ f.slots, ¬ ((c - BitVec.ofNat 64 d).toNat + off p.1 ≤ a ∧
          a < (c - BitVec.ofNat 64 d).toNat + off p.1 + p.2.size)) ∧
      (Clif.enterSlots f mem).2.place = some ⟨(c - BitVec.ofNat 64 d) :: c :: sps, fr, none⟩ := by
  let sp := c - BitVec.ofNat 64 d
  let acc : List (Clif.SlotId × Nat) × Clif.Mem :=
    ([], { mem with place := some ⟨sp :: c :: sps, fr, none⟩ })
  have e : Clif.enterSlots f mem = f.slots.foldl (Clif.placeStep sp off) acc := by
    simp only [Clif.enterSlots, hp, hf, List.headD]
    rfl
  rw [e]
  obtain ⟨h1, h2, h3, h4⟩ := Clif.placeSlots_spec sp off f.slots acc
  exact ⟨h1.trans (List.nil_append _), h2, h3, h4, (Clif.placeSlots_facts sp off f.slots acc).1⟩

theorem spv_enter (F : LFn) (x : ArmState) : spv (enter F x) = spv x :=
  r_enter (by simp) (by simp) F x

/-- **The callee's slots are outside its world's private set** (`Chain.slot_not_F` on the
two-activation chain). -/
theorem slot_not_F {L : Link} {RA : RL} (hRA : RA.Wf) (hcin : CodeIn L RA) {n : String}
    {FB : LFn} (hB : (n, FB) ∈ L.fns) {x : ArmState} {KB : Nat}
    (hRB : (L.act FB (enter FB x) KB RA.FK).Wf) (hn : Nested RA (L.act FB (enter FB x) KB RA.FK))
    {a : BitVec 64} (hs : slotArea (L.act FB (enter FB x) KB RA.FK) a) :
    ¬ (L.act FB (enter FB x) KB RA.FK).F a := by
  refine Chain.slot_not_F (T := L.act FB (enter FB x) KB RA.FK) (rest := [RA]) ⟨hn, trivial⟩
    (fun R hR => ?_) (fun R hR a ha => ?_) (by simp) hs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact hRB
    · exact hRA
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    show ¬ Region RA a
    rcases hR with rfl | rfl
    · exact hcin.notRegion hRA hB (enter_program FB x) ha
    · exact code_not_region hRA ha

/-- **The callee's code is in the caller's private set.** -/
theorem code_F {L : Link} {RA : RL} (hRA : RA.Wf) (hcin : CodeIn L RA) {n : String}
    {FB : LFn} (hB : (n, FB) ∈ L.fns) {x : ArmState} {a : BitVec 64}
    (ha : CodeAddr (enter FB x) a) : RA.F a := by
  rcases hcin n FB hB with ⟨hfb, hbase⟩ | h'
  · have hc : CodeAddr RA.s0 a := by
      unfold CodeAddr at ha ⊢
      rwa [hRA.prog0, ← hfb, ← hbase, ← enter_program FB x]
    exact Or.inl (Or.inl (Or.inr (Or.inr hc)))
  obtain ⟨j, hj, hd⟩ := codeAddr_words (enter_program FB x) ha
  have hG := (h' j _ (Array.getElem?_eq_getElem hj)).1 _ hd
  have e : FB.base + BitVec.ofNat 64 (4 * j) +
      BitVec.ofNat 64 (a - (FB.base + BitVec.ofNat 64 (4 * j))).toNat = a := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
  rw [e] at hG
  exact Or.inr hG

/-- **The callee's entry memory relation** (module doc): from the caller's memory `cm` at its
paused call (related to a world `wA` agreeing with `x` outside `RA.F`), the callee `FB` entered by
the `bl` from `x` with budget `KB` and kept addresses `RA.FK`, its slots placed by the oracle at the
caller's body `sp`. -/
theorem callee_relW {L : Link} {RA : RL} (hRA : RA.Wf) (hcin : CodeIn L RA) {n : String}
    {FB : LFn} (hB : (n, FB) ∈ L.fns) {x wA : ArmState} {KB : Nat}
    (hRB : (L.act FB (enter FB x) KB RA.FK).Wf) (hn : Nested RA (L.act FB (enter FB x) KB RA.FK))
    {syms : String → Option Nat} {cm : Clif.Mem} (hmr : MemRel RA.F syms cm wA)
    (hmem : ∀ a, ¬ RA.F a → x.mem a = wA.mem a) (herr : Arm.r .ERR x = .None)
    {fB : Clif.Function} {sps : List (BitVec 64)}
    {fr : String → Option (Nat × (Clif.SlotId → Nat))}
    (hpl : cm.place = some ⟨spv x :: sps, fr, none⟩)
    (hfr : fr fB.name = some (frameDrop FB.af, slotOffs FB.af fB))
    (hfits : ∀ p ∈ fB.slots, ∃ off, (slotLayout fB.slots).1.lookup p.1 = some off ∧
      FB.af.slotBase + off + p.2.size ≤ FB.af.frameSize - clobberBytes FB.af.saves) :
    RelW ⟨(L.act FB (enter FB x) KB RA.FK).F, syms, FB.af.slotBase, 0⟩ fB
      (spv (bodyOf FB.af (enter FB x))) (Clif.enterSlots fB cm).1 (Clif.enterSlots fB cm).2
      (bodyOf FB.af (enter FB x)) := by
  obtain ⟨hsl, hsym, hal, hby, -⟩ := enterSlots_at hpl hfr
  have hsp0 : spv (bodyOf FB.af (enter FB x)) = spv x - BitVec.ofNat 64 (frameDrop FB.af) := by
    rw [spv_bodyOf, spv_enter]
  have hspB : (L.act FB (enter FB x) KB RA.FK).spB = spv x - BitVec.ofNat 64 (frameDrop FB.af) := by
    show spv (enter FB x) - _ = _; rw [spv_enter]; rfl
  obtain ⟨hB1, hB2⟩ := spB_toNat hRB
  have hsb : (L.act FB (enter FB x) KB RA.FK).fr.size ≤ FB.af.slotBase := by
    have := (lowerRFunc_ok hRB.alloc).1.2.1
    exact this ▸ Nat.le_refl _
  have hspx : (spv (L.act FB (enter FB x) KB RA.FK).s0).toNat = (spv x).toNat := by
    show (spv (enter FB x)).toNat = _; rw [spv_enter]
  have hfs : FB.af.frameSize ≤ frameDrop FB.af := by
    rcases size_le_drop hRB with h | h
    · exact h.2
    · simp only [act_af] at h; omega
  have hsB : (spv x - BitVec.ofNat 64 (frameDrop FB.af)).toNat =
      (spv x).toNat - frameDrop FB.af := by rw [← hspB, hB1, hspx]; rfl
  -- the slot allocations end below the caller's body `sp`
  have hbnd : ∀ p ∈ fB.slots, (spv x - BitVec.ofNat 64 (frameDrop FB.af)).toNat +
      slotOffs FB.af fB p.1 + p.2.size ≤ (spv x).toNat := by
    intro p hp
    obtain ⟨off, hoff, hle⟩ := hfits p hp
    simp only [slotOffs, hoff, Option.getD_some]
    have : frameDrop FB.af ≤ (spv x).toNat := by
      have := hB2; rw [hspx] at this; simp only [act_af] at this; omega
    omega
  -- the slot allocations are in the callee's slot area, outside its `RL.F`
  have hslotF : ∀ p ∈ fB.slots, ∀ k < p.2.size,
      ¬ (L.act FB (enter FB x) KB RA.FK).F (BitVec.ofNat 64
        ((spv x - BitVec.ofNat 64 (frameDrop FB.af)).toNat + slotOffs FB.af fB p.1 + k)) := by
    intro p hp k hk
    have hb := hbnd p hp
    obtain ⟨off, hoff, hle⟩ := hfits p hp
    simp only [slotOffs, hoff, Option.getD_some] at hb ⊢
    have hlt := (spv x).isLt
    refine slot_not_F hRA hcin hB hRB hn ?_
    unfold slotArea
    have e : (BitVec.ofNat 64 ((spv x - BitVec.ofNat 64 (frameDrop FB.af)).toNat +
        (FB.af.slotBase + off) + k) - (L.act FB (enter FB x) KB RA.FK).spB).toNat =
        FB.af.slotBase + off + k := by
      rw [hspB]; bv_omega
    rw [e]; simp only [act_af] at hsb ⊢; omega
  refine ⟨⟨⟨fun a b hv hb => ?_, fun a k hv => ?_, hsym.trans hmr.symbols⟩, fun id b hl => ?_,
    outRel_zero _ _ _⟩, rfl, ?_⟩
  · obtain ⟨hb', hnot⟩ := hby a b hb
    simp only [Clif.Mem.valid, List.any_eq_true] at hv
    obtain ⟨y, hy, hcy⟩ := hv
    rcases hal y hy with hy' | ⟨p, hp, rfl⟩
    · have hv' : cm.valid a 1 = true := List.any_eq_true.mpr ⟨y, hy', hcy⟩
      have hnF := (hmr.valid a 1 hv').2 0 (by omega)
      simp only [Nat.add_zero] at hnF
      rw [← hmr.bytes a b hv' hb']
      simp only [Arm.read_mem, Arm.read_store, mem_bodyOf, enter_mem]
      rw [hmem _ hnF]
    · simp only [Clif.Alloc.contains, Bool.and_eq_true, decide_eq_true_eq] at hcy
      exact absurd ⟨hcy.1, by omega⟩ (hnot p hp)
  · simp only [Clif.Mem.valid, List.any_eq_true] at hv
    obtain ⟨y, hy, hcy⟩ := hv
    rcases hal y hy with hy' | ⟨p, hp, rfl⟩
    · have hv' : cm.valid a k = true := List.any_eq_true.mpr ⟨y, hy', hcy⟩
      obtain ⟨h1, h2⟩ := hmr.valid a k hv'
      refine ⟨h1, fun j hj hF => h2 j hj ?_⟩
      exact Nested.privA_sub hRB hn (fun c hc => code_F hRA hcin hB hc) _ hF
    · simp only [Clif.Alloc.contains, Bool.and_eq_true, decide_eq_true_eq] at hcy
      obtain ⟨c1, c2⟩ := hcy
      have hb := hbnd p hp
      have hlt := (spv x).isLt
      refine ⟨by omega, fun j hj => ?_⟩
      have h := hslotF p hp (a + j - ((spv x - BitVec.ofNat 64 (frameDrop FB.af)).toNat +
        slotOffs FB.af fB p.1)) (by omega)
      rwa [show (spv x - BitVec.ofNat 64 (frameDrop FB.af)).toNat + slotOffs FB.af fB p.1 +
        (a + j - ((spv x - BitVec.ofNat 64 (frameDrop FB.af)).toNat + slotOffs FB.af fB p.1)) =
        a + j by omega] at h
  · rw [hsl] at hl
    obtain ⟨p, hp, rfl, rfl⟩ := E2E.LinkSys.lookup_map_some hl
    obtain ⟨off, hoff, -⟩ := hfits p hp
    refine ⟨off, hoff, ?_⟩
    simp only [Rel.slotReg, slotOffs, hoff, Option.getD_some, hsp0]
    omega
  · rw [r_bodyOf _ _ (by simp) (by simp), r_enter (by simp) (by simp)]; exact herr

/-- **The caller's memory at its paused call** (module doc): its CLIF memory is related to a world
agreeing with the Arm state outside its world's private set. -/
theorem caller_world {RA : RL} (hX0 : IselCall.NoCall RA.X) {f : Clif.Function} {vc : VCode}
    {ctx : Ctx} {st0 : LState} {R : Reg → Reg} {gn : Nat → Nat} {bl : List Driver.BLow}
    {A : Nat → Nat → List Clif.ValueId} {Γ : E2E.Rel} {c : BitVec 64} {env : Clif.Env}
    {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}
    (H : DriverHypT f vc ctx st0 R gn bl A (csem RA.F RA.ctx RA.X) (RelW Γ f c) env p)
    (hchk : IselCheck.threadCheckBlC f bl = true) {Lp : Nat → Prop} {ss ss' : Array (Array Nat)}
    (H3 : PrepThread.PrepFacts vc RA.vc Lp ss ss') {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hc : CheckedAt RA.vc RA.rf cc ins a0) {r₀ : Reg → CV} {s' : Clif.State}
    {vV' vP' : VState CV ArmState} {cM' : MState CV ArmState} {x : ArmState}
    (hq : Q RA x (.run cM')) (hP : Pause RA (.run cM'))
    (hat : IselCall.AtCallS s') (hm2 : Driver.Match f ctx R gn bl A (RelW Γ f c) slots s' vV')
    (hm3 : PrepThread.PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (VCodeThread.cEvs RA.F RA.ctx) Lp ss'
      (.run vV') (.run vP'))
    (hm4 : MatchRun cc ins ckeep r₀ cM' vP') :
    ∃ w, MemRel Γ.F Γ.syms s'.mem w ∧ (∀ a, ¬ RA.F a → x.mem a = w.mem a) ∧
      Arm.r .ERR x = .None ∧ spv x = RA.spB := by
  obtain ⟨b, k, allocs, its, m, w, vb, info, rfl, -, -, -, b0, rfl, -, -⟩ :=
    CallResumeAll.atCall_of_pause hX0 H hchk H3 hc hP hat hm2 hm3 hm4
  have hst := q_stRel hq
  exact ⟨w, hm2.2.2.2.1.1.1, fun a ha => hst.world.2.1 a ha, hst.err, hst.sp⟩

end Concurrency.CallEntryRel
