import FV.Opt.TailLoop
import FV.Opt.Proof.SimpDen
import FV.Opt.Proof.SemSimX
import FV.Opt.Proof.SimpSim
import FV.Opt.Proof.SimWin
import FV.E2E.LinkPlace
import FV.E2E.Statement

/-! # Self tail calls as loops refine the program (S8, #32)

`Opt.TailLoop.TailRel P P'`: the functions of `P'` are those of `P`, each either unchanged or
`Opt.TailLoop.loop` of it (`FV/Opt/TailLoop.lean`). **`TailRel.refines`**: a whole-program run of
`P` from an entry of a function is refined by the run of `P'` from the entry of its counterpart
(same arguments, slots and memory): a return is the same return, a trap the same trap; and when
the source run returns or traps, the target run's call depth is bounded by the source run's
(`Clif.DepthLe`): a self `return_call` keeps the callers in both runs, the target loops.

Premises: distinct function names in `P` (a self `return_call` re-enters the function itself),
externs that keep the slot-placement oracle (`Clif.EnvKeepsPlace`), and an entry memory whose
oracle stack is consistent (`SpsOk`: the running activation's stack pointer is what entering
it pushed, `spOf`). Under these, `Clif.run`'s self `return_call` of a function without slots
gives back the memory it starts from (`selfTail_mem`): it frees no slot, pops the activation's
stack pointer and pushes the same one.

The simulation (`TR`): equal memories, the callers pairwise related, frames related by `FRm m`
— `m = false`: the same function, registers extended (`Valuation.Le`), the same slots,
statements and terminator; `m = true`: the source frame's function `f` is eligible
(`eligB`), the target's is `loop f`, the terminator is `termT f b0 t` of the source's `t`.
Each source step is matched by one target step, or two when it enters a transformed function
(the new entry block's `jump`, `NextRel`).
-/

namespace Opt.TailLoop

open Clif

set_option autoImplicit false

/-! ## Registers -/

theorem le_refl' (r : Regs) : Valuation.Le r r := fun _ _ h => h

theorem le_empty (r : Regs) : Valuation.Le Regs.empty r := fun _ _ h => by cases h

theorem get_le {fr fr' : Frame} (h : Valuation.Le fr.regs fr'.regs) {x : ValueId} {v : Val}
    (hx : fr.get x = .ok v) : fr'.get x = .ok v := by
  simp only [Frame.get] at hx ⊢
  cases ha : fr.regs x with
  | none => simp [ha, Res.ofOption] at hx
  | some a => simp [ha, Res.ofOption] at hx; subst hx; simp [Res.ofOption, h x a ha]

theorem getMany_le {fr fr' : Frame} (h : Valuation.Le fr.regs fr'.regs) :
    ∀ {xs : List ValueId} {vs : List Val}, fr.getMany xs = .ok vs → fr'.getMany xs = .ok vs
  | [], _, hx => hx
  | x :: xs, vs, hx => by
    simp only [Frame.getMany, Res.bind_eq_ok, Res.pure_eq_ok] at hx ⊢
    obtain ⟨a, ha, vs', hvs, rfl⟩ := hx
    exact ⟨a, get_le h ha, vs', getMany_le h hvs, rfl⟩

theorem setMany_le : ∀ {r r' : Regs} (_ : Valuation.Le r r') {xs : List ValueId} {vs : List Val}
    {q : Regs}, r.setMany xs vs = some q → ∃ q', r'.setMany xs vs = some q' ∧ Valuation.Le q q'
  | _, _, h, [], [], _, hq => by cases hq; exact ⟨_, rfl, h⟩
  | _, _, _, [], _ :: _, _, hq => by cases hq
  | _, _, _, _ :: _, [], _, hq => by cases hq
  | r, r', h, x :: xs, v :: vs, q, hq => by
    simp only [Regs.setMany] at hq ⊢
    refine setMany_le (r := r.set x v) (r' := r'.set x v) (fun y a hy => ?_) hq
    by_cases hyx : y = x
    · subst hyx; simpa using hy
    · rw [Regs.set_other _ _ hyx] at hy ⊢; exact h y a hy

/-! ## The transformed function -/

theorem loop_hdr (f : Function) : (loop f).name = f.name ∧ (loop f).sig = f.sig ∧
    (loop f).slots = f.slots ∧ (loop f).globals = f.globals ∧ (loop f).externs = f.externs ∧
    (loop f).sigDecls = f.sigDecls := by
  unfold loop
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem loop_of_not {f : Function} (h : eligB f = false) : loop f = f := by
  unfold loop; split
  · rfl
  · simp [h]

/-- The first block's id. -/
def b0id (f : Function) : BlockId := (f.blocks.head?.map (·.id)).getD 0

theorem foldl_newId_ge : ∀ (l : List Block) (m : Nat), m ≤ l.foldl (fun m b => max m (b.id + 1)) m
  | [], _ => Nat.le_refl _
  | b :: l, m => Nat.le_trans (Nat.le_max_left m (b.id + 1)) (foldl_newId_ge l _)

theorem foldl_newId_gt : ∀ (l : List Block) (m : Nat), ∀ b ∈ l,
    b.id < l.foldl (fun m b => max m (b.id + 1)) m
  | [], _, _, hb => by cases hb
  | c :: l, m, b, hb => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Nat.lt_of_lt_of_le (by omega) (foldl_newId_ge l (max m (b.id + 1)))
    · exact foldl_newId_gt l _ b hb

theorem newId_gt {f : Function} {b : Block} (hb : b ∈ f.blocks) : b.id < newId f :=
  foldl_newId_gt _ _ b hb

/-- The blocks of an eligible function's `loop`. -/
theorem loop_blocks {f : Function} {b0 : Block} {bs : List Block} (hb : f.blocks = b0 :: bs)
    (he : eligB f = true) :
    (loop f).blocks = entryBlock f b0 :: f.blocks.map (blockT f b0.id) := by
  unfold loop; rw [hb]; simp only [he, if_true]

theorem b0id_eq {f : Function} {b0 : Block} {bs : List Block} (hb : f.blocks = b0 :: bs) :
    b0id f = b0.id := by simp [b0id, hb]

/-- A block of `f` is found in `loop f` with its self `return_call`s replaced. -/
theorem loop_block? {f : Function} (he : eligB f = true) {d : BlockId} {b : Block}
    (hd : f.block? d = some b) : (loop f).block? d = some (blockT f (b0id f) b) := by
  cases hb : f.blocks with
  | nil => simp [Function.block?, hb] at hd
  | cons b0 bs =>
    have hbm : b ∈ f.blocks := List.mem_of_find?_eq_some hd
    have hid : b.id = d := by simpa using List.find?_some hd
    rw [Function.block?, loop_blocks hb he, b0id_eq hb, List.find?_cons]
    have hne : ((entryBlock f b0).id == d) = false := by
      have h1 : (entryBlock f b0).id = newId f := rfl
      rw [beq_eq_false_iff_ne, h1]
      intro heq; have := newId_gt hbm; rw [hid, ← heq] at this; exact Nat.lt_irrefl _ this
    rw [hne]
    simp only [List.find?_map]
    have : (f.blocks.find? ((· == d) ∘ (·.id) ∘ blockT f b0.id)) = some b := by
      have h2 : ((· == d) ∘ (·.id) ∘ blockT f b0.id) = fun c : Block => c.id == d := by
        funext c; rfl
      rw [h2]; exact hd
    rw [show (fun x : Block => x.id == d) ∘ blockT f b0.id = (· == d) ∘ (·.id) ∘ blockT f b0.id
      from rfl, this]
    rfl

theorem loop_entry {f : Function} {b0 : Block} {bs : List Block} (hb : f.blocks = b0 :: bs)
    (he : eligB f = true) : (loop f).entry? = some (entryBlock f b0) := by
  simp [Function.entry?, loop_blocks hb he]

theorem eligB_spec {f : Function} (he : eligB f = true) :
    f.slots = [] ∧ (∀ b ∈ f.blocks, b.term.isTry = false) ∧
      ∃ b0 bs, f.blocks = b0 :: bs ∧ b0.params.map (·.2) = AbiParam.tys f.sig.params := by
  simp only [eligB, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true, Bool.not_eq_true'] at he
  obtain ⟨⟨⟨h1, h2⟩, -⟩, h4⟩ := he
  refine ⟨h1, h2, ?_⟩
  cases hb : f.blocks with
  | nil => rw [hb] at h4; cases h4
  | cons b0 bs => rw [hb] at h4; exact ⟨b0, bs, rfl, by simpa using h4⟩

theorem termT_isTry {f : Function} {b0 : BlockId} {t : Terminator} (h : t.isTry = false) :
    (termT f b0 t).isTry = false := by
  cases t with
  | returnCall fn args => simp only [termT]; split <;> rfl
  | _ => simpa [termT] using h

theorem termT_of_not {f : Function} {b0 : BlockId} {t : Terminator}
    (h : ∀ fn args, t = .returnCall fn args → selfTail f fn = false) : termT f b0 t = t := by
  cases t with
  | returnCall fn args => simp [termT, h fn args rfl]
  | _ => rfl

/-! ## Programs -/

/-- The target function `g` of a source function `f`: `f` itself or `loop f`. -/
def TP (f g : Function) : Prop := g = f ∨ g = loop f

/-- `P'`'s functions are `P`'s, each unchanged or `loop` of it. -/
def TailRel (P P' : Program) : Prop := Pw2 TP P.funcs P'.funcs

theorem tp_name {f g : Function} (h : TP f g) : g.name = f.name := by
  rcases h with rfl | rfl
  · rfl
  · exact (loop_hdr f).1

theorem tp_sig {f g : Function} (h : TP f g) : g.sig = f.sig := by
  rcases h with rfl | rfl
  · rfl
  · exact (loop_hdr f).2.1

theorem tp_externs {f g : Function} (h : TP f g) : g.externs = f.externs := by
  rcases h with rfl | rfl
  · rfl
  · exact (loop_hdr f).2.2.2.2.1

theorem find?_rel : ∀ {fs gs : List Function}, Pw2 TP fs gs → ∀ (q : String → Bool),
    (∀ f, fs.find? (fun f => q f.name) = some f →
      ∃ g, gs.find? (fun g => q g.name) = some g ∧ TP f g) ∧
    (fs.find? (fun f => q f.name) = none → gs.find? (fun g => q g.name) = none)
  | [], [], .nil, _ => ⟨fun _ h => by simp at h, fun _ => rfl⟩
  | f :: fs, g :: gs, .cons hfg hr, q => by
    have ih := find?_rel hr q
    simp only [List.find?_cons, tp_name hfg]
    split
    · exact ⟨fun f' h => by cases h; exact ⟨g, rfl, hfg⟩, fun h => by cases h⟩
    · exact ih

theorem TailRel.func? {P P' : Program} (h : TailRel P P') (n : String) :
    (∀ f, P.func? n = some f → ∃ g, P'.func? n = some g ∧ TP f g) ∧
      (P.func? n = none → P'.func? n = none) :=
  find?_rel h (· == n)

theorem externNames_rel : ∀ {fs gs : List Function}, Pw2 TP fs gs →
    gs.flatMap (fun f => f.externs.map (·.2.name)) = fs.flatMap (fun f => f.externs.map (·.2.name))
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons hfg hr => by
    simp only [List.flatMap_cons, tp_externs hfg, externNames_rel hr]

theorem TailRel.externNames {P P' : Program} (h : TailRel P P') :
    P'.externNames = P.externNames := externNames_rel h

theorem find?_of_mem : ∀ {l : List Function}, (l.map (·.name)).Nodup → ∀ {g : Function},
    g ∈ l → l.find? (·.name == g.name) = some g
  | [], _, _, hg => by cases hg
  | h :: hs, hnd, g, hg => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hg with rfl | hg
    · simp
    · have hne : h.name ≠ g.name := fun he => hnd.1 ⟨g, hg, he.symm⟩
      have hb : (h.name == g.name) = false := by simpa using hne
      simp only [List.find?_cons, hb]
      exact find?_of_mem hnd.2 hg

theorem func?_of_mem {P : Program} (hnd : (P.funcs.map (·.name)).Nodup) {g : Function}
    (hg : g ∈ P.funcs) : P.func? g.name = some g := find?_of_mem hnd hg

theorem func?_self {P : Program} {n : String} {g : Function} (h : P.func? n = some g) :
    P.func? g.name = some g := by
  have := (Program.func?_some h).2; rw [this]; exact h

/-! ## The slot-placement oracle's stack -/

/-- The stack pointer that entering the function named `n` pushes on the oracle stack `xs`
(`Clif.enterSlots`). -/
def spOf (fr : String → Option (Nat × (SlotId → Nat))) (n : String) (xs : List (BitVec 64)) :
    BitVec 64 :=
  match fr n with
  | some (d, _) => xs.headD 0 - BitVec.ofNat 64 d
  | none => xs.headD 0

/-- Each activation's stack pointer (one per name, the running one first) is what entering it
pushed. -/
def Chain (fr : String → Option (Nat × (SlotId → Nat))) : List String → List (BitVec 64) → Prop
  | [], _ => True
  | n :: ns, x :: xs => x = spOf fr n xs ∧ Chain fr ns xs
  | _ :: _, [] => False

/-- The names of the activations of a state, the running one first. -/
def names (s : State) : List String := s.frame.func.name :: s.callers.map (·.1.func.name)

/-- **The oracle stack of a state is consistent**: each activation's stack pointer is what
entering its function pushed (vacuous without the oracle). -/
def SpsOk (s : State) : Prop := ∀ pl, s.mem.place = some pl → Chain pl.frame (names s) pl.sps

/-- `enterSlots_sps` also under the slot-byte oracle `Place.init` (which it may advance). -/
theorem enterSlots_sps_init (f : Function) (mem : Mem) :
    (mem.place = none → (enterSlots f mem).2.place = none) ∧
    ∀ pl, mem.place = some pl → ∃ ini,
      (enterSlots f mem).2.place =
        some { pl with sps := spOf pl.frame f.name pl.sps :: pl.sps, init := ini } := by
  refine ⟨(enterSlots_place_init f mem).1, fun pl h => ?_⟩
  obtain ⟨sp, ini, hsp, -⟩ := (enterSlots_place_init f mem).2 pl h
  refine ⟨ini, ?_⟩
  rw [hsp]
  cases hf : pl.frame f.name with
  | none =>
    have e : (enterSlots f mem).2.place = some { pl with sps := pl.sps.headD 0 :: pl.sps } := by
      simp only [enterSlots, h, hf]
      exact (bumpSlots_facts f.slots _).1
    rw [hsp] at e
    simp only [Option.some.injEq, Place.mk.injEq] at e
    simp only [spOf, hf, e.1]
  | some p =>
    obtain ⟨d, off⟩ := p
    have e : ∀ m0 : Mem,
        (placeSlots f.slots (pl.sps.headD 0 - BitVec.ofNat 64 d) off m0).2.place = m0.place :=
      fun m0 => (placeSlots_facts _ _ f.slots ([], m0)).1
    have e2 : ∃ ini', (enterSlots f mem).2.place =
        some { pl with sps := (pl.sps.headD 0 - BitVec.ofNat 64 d) :: pl.sps, init := ini' } := by
      simp only [enterSlots, h, hf, initSlots_place, e]
      cases pl.init with
      | none => exact ⟨_, rfl⟩
      | some i =>
        by_cases hs : f.slots.isEmpty
        · exact ⟨some i, by simp only [initPlace, hs, if_true]⟩
        · exact ⟨some i.succ, by simp only [initPlace, hs, Option.map_some, Place.advance]; rfl⟩
    obtain ⟨ini', e2⟩ := e2
    rw [hsp] at e2
    simp only [Option.some.injEq, Place.mk.injEq] at e2
    simp only [spOf, hf, e2.1]

theorem enterSlots_sps (f : Function) (mem : Mem)
    (hi : ∀ pl, mem.place = some pl → pl.init = none) :
    (mem.place = none → (enterSlots f mem).2.place = none) ∧
    ∀ pl, mem.place = some pl →
      (enterSlots f mem).2.place = some { pl with sps := spOf pl.frame f.name pl.sps :: pl.sps } := by
  refine ⟨(enterSlots_sps_init f mem).1, fun pl h => ?_⟩
  obtain ⟨ini, e⟩ := (enterSlots_sps_init f mem).2 pl h
  obtain ⟨sp, ini', hsp, hini⟩ := (enterSlots_place_init f mem).2 pl h
  have hx : ini = pl.init := by
    rw [hsp] at e
    have := congrArg (fun o => o.map Place.init) e
    simp only [Option.map_some, Option.some.injEq] at this
    rw [← this]; exact hini (.inl (hi pl h))
  rw [e, hx]

/-- `enterFunc_sps` also under the slot-byte oracle `Place.init` (which it may advance). -/
theorem enterFunc_sps_init {f : Function} {vals : List Val} {mem mem1 : Mem} {fr1 : Frame}
    (h : enterFunc f vals mem = .ok (fr1, mem1)) :
    (mem.place = none → mem1.place = none) ∧
    ∀ pl, mem.place = some pl → ∃ ini,
      mem1.place = some { pl with sps := spOf pl.frame f.name pl.sps :: pl.sps, init := ini } := by
  obtain ⟨_, _, _, _, _, _, he, _⟩ := Opt.enterFunc_ok h
  have := enterSlots_sps_init f mem
  rw [he] at this
  exact this

theorem enterFunc_sps {f : Function} {vals : List Val} {mem mem1 : Mem} {fr1 : Frame}
    (h : enterFunc f vals mem = .ok (fr1, mem1)) (hi : ∀ pl, mem.place = some pl → pl.init = none) :
    (mem.place = none → mem1.place = none) ∧
    ∀ pl, mem.place = some pl →
      mem1.place = some { pl with sps := spOf pl.frame f.name pl.sps :: pl.sps } := by
  obtain ⟨_, _, _, _, _, _, he, _⟩ := Opt.enterFunc_ok h
  have := enterSlots_sps f mem hi
  rw [he] at this
  exact this

theorem leave_sps (mem : Mem) (bs : List Nat) :
    (mem.place = none → ((mem.free bs).leave).place = none) ∧
    ∀ pl, mem.place = some pl → ((mem.free bs).leave).place = some { pl with sps := pl.sps.tail } := by
  refine ⟨fun h => ?_, fun pl h => ?_⟩ <;> simp [Mem.leave, Mem.free, h]

theorem enterSlots_congr {f g : Function} (hn : g.name = f.name) (hs : g.slots = f.slots)
    (mem : Mem) : enterSlots g mem = enterSlots f mem := by
  simp only [enterSlots, hn, hs]

theorem enterSlots_nil {f : Function} (hs : f.slots = []) (mem : Mem) :
    (enterSlots f mem).1 = [] := by
  unfold enterSlots
  split
  · simp [bumpSlots, hs]
  · split <;> simp [bumpSlots, placeSlots, hs]

/-- **A self `return_call` of a function without slots gives back the memory**: on a consistent
oracle stack, leaving the activation pops the stack pointer that entering it again pushes. -/
theorem selfTail_mem {f : Function} (hs : f.slots = []) {mem : Mem} {ns : List String}
    (hc : ∀ pl, mem.place = some pl → Chain pl.frame (f.name :: ns) pl.sps) :
    enterSlots f ((mem.free []).leave) = ([], mem) := by
  have hfree : mem.free [] = mem := by cases mem; simp [Mem.free]
  rw [hfree]
  cases hp : mem.place with
  | none =>
    have hl : mem.leave = mem := by simp [Mem.leave, hp]
    rw [hl]; simp [enterSlots, hp, bumpSlots, hs]
  | some pl =>
    obtain ⟨sps, frm, ini⟩ := pl
    have hch := hc _ hp
    cases sps with
    | nil => exact absurd hch (by simp [Chain])
    | cons x xs =>
      simp only [Chain] at hch
      obtain ⟨hx, -⟩ := hch
      have hl : mem.leave = { mem with place := some ⟨xs, frm, ini⟩ } := by simp [Mem.leave, hp]
      rw [hl]
      simp only [spOf] at hx
      cases hfr : frm f.name with
      | none =>
        simp only [hfr] at hx
        simp only [enterSlots, hfr, bumpSlots, hs, List.foldl_nil, Prod.mk.injEq, true_and]
        rw [← hx]
        cases mem; simp_all
      | some p =>
        obtain ⟨d, off⟩ := p
        simp only [hfr] at hx
        simp only [enterSlots, hfr, placeSlots, hs, List.foldl_nil, initSlots_nil, Prod.mk.injEq,
          true_and]
        rw [← hx]
        cases mem; simp_all

/-! ## The simulation relation -/

/-- **Frames related in mode `m`** (module doc). -/
structure FRm (P : Program) (m : Bool) (fr fr' : Frame) : Prop where
  func : fr'.func = if m then loop fr.func else fr.func
  regs : Valuation.Le fr.regs fr'.regs
  slots : fr'.slots = fr.slots
  body : fr'.body = fr.body
  term : fr'.term = if m then termT fr.func (b0id fr.func) fr.term else fr.term
  elig : m = true → eligB fr.func = true
  noTry : m = true → fr.term.isTry = false
  self : m = true → P.func? fr.func.name = some fr.func
  noSlots : m = true → fr.slots = []

def FR (P : Program) (fr fr' : Frame) : Prop := ∃ m, FRm P m fr fr'

/-- Callers pairwise related, with the same pending results. -/
def CR (P : Program) (cs cs' : List (Frame × List ValueId)) : Prop :=
  Pw2 (fun a b => b.2 = a.2 ∧ FR P a.1 b.1) cs cs'

/-- **Related states**: the same memory, related frames and callers. -/
structure TR (P : Program) (s s' : State) : Prop where
  mem : s'.mem = s.mem
  frame : FR P s.frame s'.frame
  callers : CR P s.callers s'.callers

theorem FRm.hdr {P : Program} {m : Bool} {fr fr' : Frame} (h : FRm P m fr fr') :
    fr'.func.name = fr.func.name ∧ fr'.func.sig = fr.func.sig ∧ fr'.func.slots = fr.func.slots ∧
      fr'.func.globals = fr.func.globals ∧ fr'.func.externs = fr.func.externs ∧
      fr'.func.sigDecls = fr.func.sigDecls := by
  rw [h.func]; cases m
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact loop_hdr _

theorem FRm.update {P : Program} {m : Bool} {fr fr' : Frame} (h : FRm P m fr fr') {r r' : Regs}
    (hr : Valuation.Le r r') (b : List Stmt) :
    FRm P m { fr with regs := r, body := b } { fr' with regs := r', body := b } where
  func := h.func
  regs := hr
  slots := h.slots
  body := rfl
  term := h.term
  elig := h.elig
  noTry := h.noTry
  self := h.self
  noSlots := h.noSlots

theorem FRm.refl (P : Program) (fr : Frame) : FRm P false fr fr where
  func := rfl
  regs := le_refl' _
  slots := rfl
  body := rfl
  term := rfl
  elig := fun h => by cases h
  noTry := fun h => by cases h
  self := fun h => by cases h
  noSlots := fun h => by cases h

theorem CR.length {P : Program} {cs cs' : List (Frame × List ValueId)} (h : CR P cs cs') :
    cs'.length = cs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Entering a block keeps the relation. -/
theorem enterBlock_rel {P : Program} {m : Bool} {fr fr' : Frame} (h : FRm P m fr fr')
    {bc : BlockCall} {fr1 : Frame} (he : enterBlock fr bc = .ok fr1) :
    ∃ fr1', enterBlock fr' bc = .ok fr1' ∧ FRm P m fr1 fr1' := by
  obtain ⟨b, args, regs, hb, ha, ht, hr, rfl⟩ := Opt.enterBlock_ok he
  have hbm : b ∈ fr.func.blocks := List.mem_of_find?_eq_some hb
  have hb' : fr'.func.block? bc.block = some (if m then blockT fr.func (b0id fr.func) b else b) := by
    rw [h.func]; cases m
    · exact hb
    · exact loop_block? (h.elig rfl) hb
  obtain ⟨regs', hr', hle⟩ := setMany_le h.regs hr
  have hpar : (if m then blockT fr.func (b0id fr.func) b else b).params = b.params := by
    cases m <;> rfl
  refine ⟨⟨fr'.func, regs', fr'.slots, b.body,
      (if m then blockT fr.func (b0id fr.func) b else b).term⟩, ?_, ?_⟩
  · have hp2 := hpar
    simp only [enterBlock, hb', Res.ofOption_some, Res.ok_bind, getMany_le h.regs ha, hp2, checkTys,
      ht, beq_self_eq_true, Res.check_true, hr', Res.pure_eq]
    cases m <;> rfl
  · exact {
      func := h.func
      regs := hle
      slots := h.slots
      body := by cases m <;> rfl
      term := by cases m <;> rfl
      elig := h.elig
      noTry := fun hm => (eligB_spec (h.elig hm)).2.1 b hbm
      self := h.self
      noSlots := h.noSlots }

/-! ## Results of steps -/

/-- `r'` gives what `r` gives, unless `r` is stuck. -/
def RR {α : Type} (r r' : Res α) : Prop :=
  (∀ a, r = .ok a → r' = .ok a) ∧ (∀ c, r = .trap c → r' = .trap c)

theorem RR.refl {α : Type} (r : Res α) : RR r r := ⟨fun _ h => h, fun _ h => h⟩

theorem RR.bind {α β : Type} {r r' : Res α} {f f' : α → Res β} (h : RR r r')
    (hf : ∀ a, r = .ok a → RR (f a) (f' a)) : RR (r >>= f) (r' >>= f') := by
  cases r with
  | ok a =>
    rw [h.1 a rfl]
    exact hf a rfl
  | trap c =>
    rw [h.2 c rfl]
    exact ⟨fun _ h => by simp [bind, Res.bind] at h, fun _ h => by simpa [bind, Res.bind] using h⟩
  | stuck m => exact ⟨fun _ h => by simp [bind, Res.bind] at h, fun _ h => by simp [bind, Res.bind] at h⟩

theorem getMany_ne_trap (fr : Frame) : ∀ (xs : List ValueId) (c : TrapCode), fr.getMany xs ≠ .trap c
  | [], _, h => by cases h
  | x :: xs, c, h => by
    simp only [Frame.getMany, Frame.get] at h
    cases hx : fr.regs x with
    | none => simp [hx, Res.ofOption, bind, Res.bind] at h
    | some v =>
      simp only [hx, Res.ofOption] at h
      cases hm : fr.getMany xs with
      | ok _ => simp [hm, bind, Res.bind, pure] at h
      | trap c' => exact getMany_ne_trap fr xs c' hm
      | stuck _ => simp [hm, bind, Res.bind] at h

theorem getMany_RR {fr fr' : Frame} (h : Valuation.Le fr.regs fr'.regs) (xs : List ValueId) :
    RR (fr.getMany xs) (fr'.getMany xs) :=
  ⟨fun _ ha => getMany_le h ha, fun c hc => absurd hc (getMany_ne_trap fr xs c)⟩

theorem get_RR {fr fr' : Frame} (h : Valuation.Le fr.regs fr'.regs) (x : ValueId) :
    RR (fr.get x) (fr'.get x) := by
  refine ⟨fun _ ha => get_le h ha, fun c hc => ?_⟩
  simp only [Frame.get, Res.ofOption] at hc; split at hc <;> cases hc

/-- The target state `t1'` a target step reaches matches the source state `t`, or one more
target step (keeping the callers, the new entry block's `jump`) reaches a match. -/
def NextRel (env : Env) (P P' : Program) (t t1' : State) : Prop :=
  TR P t t1' ∨ ∃ t2', step env P' t1' = .next t2' ∧ t2'.callers = t1'.callers ∧ TR P t t2'

/-- The target step result matches the source step result (module doc); a source step keeps
the oracle stack consistent. -/
def StepRel (env : Env) (P P' : Program) : StepResult → StepResult → Prop
  | .next t, r' => SpsOk t ∧ ∃ t1', r' = .next t1' ∧ NextRel env P P' t t1'
  | .done v m, r' => r' = .done v m
  | .trapped c, r' => r' = .trapped c
  | .stuck _, _ => True

theorem ofRes_rel {env : Env} {P P' : Program} {α : Type} {r r' : Res α} (h : RR r r')
    {k k' : α → StepResult} (hk : ∀ a, r = .ok a → StepRel env P P' (k a) (k' a)) :
    StepRel env P P' (StepResult.ofRes r k) (StepResult.ofRes r' k') := by
  cases r with
  | ok a => rw [h.1 a rfl]; exact hk a rfl
  | trap c => rw [h.2 c rfl]; rfl
  | stuck m => trivial

/-! ## Oracle stacks of the next states -/

theorem sps_enter {c : Function} {vals : List Val} {mem mem1 : Mem} {fr1 : Frame}
    (he : enterFunc c vals mem = .ok (fr1, mem1)) {ns : List String}
    (hc : ∀ pl, mem.place = some pl → Chain pl.frame ns pl.sps) :
    ∀ pl, mem1.place = some pl → Chain pl.frame (c.name :: ns) pl.sps := by
  intro pl1 h1
  cases hm : mem.place with
  | none => rw [(enterFunc_sps_init he).1 hm] at h1; cases h1
  | some pl =>
    obtain ⟨ini, e⟩ := (enterFunc_sps_init he).2 pl hm
    rw [e] at h1; cases h1; exact ⟨rfl, hc pl hm⟩

theorem sps_leave {mem : Mem} {bs : List Nat} {n : String} {ns : List String}
    (hc : ∀ pl, mem.place = some pl → Chain pl.frame (n :: ns) pl.sps) :
    ∀ pl, ((mem.free bs).leave).place = some pl → Chain pl.frame ns pl.sps := by
  intro pl1 h1
  cases hm : mem.place with
  | none => rw [(leave_sps mem bs).1 hm] at h1; cases h1
  | some pl =>
    rw [(leave_sps mem bs).2 pl hm] at h1; cases h1
    have := hc pl hm
    revert this
    cases pl.sps with
    | nil => simp [Chain]
    | cons x xs => exact fun h => h.2

theorem enterFunc_func {c : Function} {vals : List Val} {mem mem1 : Mem} {fr1 : Frame}
    (he : enterFunc c vals mem = .ok (fr1, mem1)) : fr1.func = c := by
  obtain ⟨_, _, _, _, _, _, _, hfr⟩ := Opt.enterFunc_ok he
  rw [hfr]

theorem callExternAt_place {env : Env} (hk : EnvKeepsPlace env) {p : Program} {mem : Mem}
    {d : Signature} {a : Nat} {vals rvals : List Val} {mem' : Mem}
    (h : callExternAt env p mem d a vals = .ok (rvals, mem')) : mem'.place = mem.place := by
  simp only [callExternAt, Res.bind_eq_ok, Res.ofOption_eq_ok, checkTys, Res.check_eq_ok] at h
  obtain ⟨n, -, g, hg, -, -, -, -, h⟩ := h
  split at h
  · rename_i rv m' hr
    split at h
    · simp only [Res.pure_eq_ok, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hk n g hg vals mem rv m' hr
    · cases h
  all_goals cases h

/-! ## Registers bound at an entry -/

theorem setMany_some : ∀ (r : Regs) (xs : List ValueId) (vs : List Val),
    xs.length = vs.length → ∃ q, r.setMany xs vs = some q
  | r, [], [], _ => ⟨r, rfl⟩
  | _, [], _ :: _, h => by cases h
  | _, _ :: _, [], h => by cases h
  | r, x :: xs, v :: vs, h => setMany_some (r.set x v) xs vs (by simpa using h)

theorem setMany_other : ∀ {r : Regs} {xs : List ValueId} {vs : List Val} {q : Regs},
    r.setMany xs vs = some q → ∀ y, y ∉ xs → q y = r y
  | _, [], [], _, h, _, _ => by cases h; rfl
  | _, [], _ :: _, _, h, _, _ => by cases h
  | _, _ :: _, [], _, h, _, _ => by cases h
  | r, x :: xs, v :: vs, q, h, y, hy => by
    simp only [Regs.setMany] at h
    rw [setMany_other h y (fun hm => hy (List.mem_cons_of_mem _ hm))]
    exact Regs.set_other _ _ (fun he => hy (he ▸ List.mem_cons_self ..))

theorem getMany_setMany : ∀ {r : Regs} {xs : List ValueId} {vs : List Val} {q : Regs},
    xs.Nodup → r.setMany xs vs = some q → ∀ fr : Frame, fr.regs = q → fr.getMany xs = .ok vs
  | _, [], [], _, _, h, fr, _ => by cases h; rfl
  | _, [], _ :: _, _, _, h, _, _ => by cases h
  | _, _ :: _, [], _, _, h, _, _ => by cases h
  | r, x :: xs, v :: vs, q, hnd, h, fr, hq => by
    simp only [Regs.setMany] at h
    have hx : x ∉ xs := (List.nodup_cons.mp hnd).1
    have hqx : q x = some v := by rw [setMany_other h x hx]; simp
    simp only [Frame.getMany, Frame.get, hq, hqx, Res.ofOption_some, Res.ok_bind,
      getMany_setMany (List.nodup_cons.mp hnd).2 h fr hq, Res.pure_eq]

theorem freshParams_snd : ∀ (base : ValueId) (ps : List (ValueId × Ty)),
    (freshParams base ps).map (·.2) = ps.map (·.2)
  | _, [] => rfl
  | base, (_, t) :: ps => by simp [freshParams, freshParams_snd (base + 1) ps]

theorem freshParams_length : ∀ (base : ValueId) (ps : List (ValueId × Ty)),
    (freshParams base ps).length = ps.length
  | _, [] => rfl
  | base, (_, t) :: ps => by simp [freshParams, freshParams_length (base + 1) ps]

theorem freshParams_ge : ∀ (base : ValueId) (ps : List (ValueId × Ty)),
    ∀ y ∈ (freshParams base ps).map (·.1), base ≤ y
  | _, [], _, hy => by cases hy
  | base, (_, t) :: ps, y, hy => by
    simp only [freshParams, List.map_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact Nat.le_refl _
    · exact Nat.le_of_succ_le (freshParams_ge (base + 1) ps y hy)

theorem freshParams_nodup : ∀ (base : ValueId) (ps : List (ValueId × Ty)),
    ((freshParams base ps).map (·.1)).Nodup
  | _, [] => List.nodup_nil
  | base, (_, t) :: ps => by
    simp only [freshParams, List.map_cons, List.nodup_cons]
    exact ⟨fun h => absurd (freshParams_ge (base + 1) ps base h) (Nat.not_succ_le_self base),
      freshParams_nodup (base + 1) ps⟩

theorem enterFunc_ne_trap (f : Function) (vals : List Val) (mem : Mem) (c : TrapCode) :
    enterFunc f vals mem ≠ .trap c := Opt.enterFunc_not_trap f vals mem c

theorem enterBlock_ne_trap (fr : Frame) (bc : BlockCall) (c : TrapCode) :
    enterBlock fr bc ≠ .trap c := by
  intro h
  simp only [enterBlock] at h
  cases hb : fr.func.block? bc.block with
  | none => simp [hb] at h
  | some b =>
    simp only [hb, Res.ofOption_some, Res.ok_bind] at h
    cases hg : fr.getMany bc.args with
    | ok a =>
      simp only [hg, Res.ok_bind, checkTys, Res.check] at h
      split at h
      · simp only [Res.ok_bind] at h
        cases hs : fr.regs.setMany (b.params.map (·.1)) a <;> simp [hs] at h
      · cases h
    | trap c' => exact getMany_ne_trap fr _ c' hg
    | stuck _ => simp [hg] at h

/-! ## Entering a function -/

/-- **Entering a callee**: the target enters its counterpart with the same memory; the
frames are related, or (a transformed callee) related after the new entry block's `jump`. -/
theorem enterFunc_rel {P P' : Program} {c g : Function} (hcg : TP c g)
    (hself : P.func? c.name = some c) {vals : List Val} {mem mem1 : Mem} {fr1 : Frame}
    (he : enterFunc c vals mem = .ok (fr1, mem1)) :
    ∃ fr1', enterFunc g vals mem = .ok (fr1', mem1) ∧ ∀ env callers callers',
      CR P callers callers' → NextRel env P P' ⟨fr1, callers, mem1⟩ ⟨fr1', callers', mem1⟩ := by
  have hsame : ∀ env callers callers', CR P callers callers' →
      NextRel env P P' ⟨fr1, callers, mem1⟩ ⟨fr1, callers', mem1⟩ :=
    fun _ _ _ hc => .inl ⟨rfl, ⟨false, FRm.refl P fr1⟩, hc⟩
  rcases hcg with rfl | rfl
  · exact ⟨fr1, he, hsame⟩
  cases hel : eligB c with
  | false => rw [loop_of_not hel]; exact ⟨fr1, he, hsame⟩
  | true =>
  obtain ⟨hs, hnt, b0, bs, hb, hpar⟩ := eligB_spec hel
  obtain ⟨fc, fregs, fsl, fbd, ftm⟩ := fr1
  obtain ⟨b, regs, hent, h1, h2, hr, hsl, hfr⟩ := Opt.enterFunc_ok he
  simp only [Frame.mk.injEq] at hfr
  obtain ⟨rfl, rfl, -, rfl, rfl⟩ := hfr
  have hb0 : b = b0 := by simp [Function.entry?, hb] at hent; exact hent.symm
  subst hb0
  have hlen : ((freshParams fc.freshValue b.params).map (·.1)).length = vals.length := by
    rw [List.length_map, freshParams_length]
    have := congrArg List.length h2; simpa using this.symm
  obtain ⟨rq, hrq⟩ := setMany_some Regs.empty _ vals hlen
  have hent' : (loop fc).entry? = some (entryBlock fc b) := loop_entry hb hel
  have h1' : vals.map (·.ty) = AbiParam.tys (loop fc).sig.params := by rw [(loop_hdr fc).2.1]; exact h1
  have h2' : vals.map (·.ty) = (entryBlock fc b).params.map (·.2) := by
    simp only [entryBlock, freshParams_snd]; exact h2
  have hes : enterSlots (loop fc) mem = (fsl, mem1) := by
    rw [enterSlots_congr (loop_hdr fc).1 (loop_hdr fc).2.2.1]; exact hsl
  refine ⟨⟨loop fc, rq, fsl, [], .jump ⟨b.id, (freshParams fc.freshValue b.params).map (·.1)⟩⟩,
    ?_, fun env callers callers' hc => .inr ?_⟩
  · rw [Opt.enterFunc_of hent' h1' h2' hrq, hes]; rfl
  · have hbl : fc.block? b.id = some b := by simp [Function.block?, hb]
    have hlb := loop_block? hel hbl
    rw [b0id_eq hb] at hlb
    obtain ⟨regs2, hr2, hle⟩ := setMany_le (le_empty rq) hr
    have hgm : (⟨loop fc, rq, fsl, [], .jump ⟨b.id, (freshParams fc.freshValue b.params).map (·.1)⟩⟩ :
        Frame).getMany ((freshParams fc.freshValue b.params).map (·.1)) = .ok vals :=
      getMany_setMany (freshParams_nodup _ _) hrq _ rfl
    have hfsl : fsl = [] := by
      have := enterSlots_nil hs mem; rw [hsl] at this; exact this
    refine ⟨⟨⟨loop fc, regs2, fsl, b.body, (blockT fc b.id b).term⟩, callers', mem1⟩, ?_, rfl, ?_⟩
    · simp only [step, stepTerm, enterBlock, hlb, Res.ofOption_some, Res.ok_bind, hgm, checkTys,
        blockT, ← h2, beq_self_eq_true, Res.check_true, hr2, Res.pure_eq, StepResult.ofRes_ok]
    · refine ⟨rfl, ⟨true, ?_⟩, hc⟩
      exact {
        func := rfl
        regs := hle
        slots := rfl
        body := rfl
        term := by simp [blockT, b0id_eq hb]
        elig := fun _ => hel
        noTry := fun _ => hnt b (by rw [hb]; exact List.mem_cons_self ..)
        self := fun _ => hself
        noSlots := fun _ => hfsl }

/-! ## Steps -/

theorem FRm.setRegs {P : Program} {m : Bool} {fr fr' : Frame} (h : FRm P m fr fr') {r r' : Regs}
    (hr : Valuation.Le r r') : FRm P m { fr with regs := r } { fr' with regs := r' } where
  func := h.func
  regs := hr
  slots := h.slots
  body := h.body
  term := h.term
  elig := h.elig
  noTry := h.noTry
  self := h.self
  noSlots := h.noSlots

theorem callArgs_RR {fr fr' : Frame} (hx : fr'.func.externs = fr.func.externs)
    (hle : Valuation.Le fr.regs fr'.regs) (fn : FnRef) (args : List ValueId) :
    RR (Opt.callArgs fr fn args) (Opt.callArgs fr' fn args) := by
  unfold Opt.callArgs
  rw [show fr'.func.extern? fn = fr.func.extern? fn by simp [Function.extern?, hx]]
  exact RR.bind (RR.refl _) fun _ _ => RR.bind (getMany_RR hle args) fun _ _ => RR.refl _

theorem tailArgs_RR {fr fr' : Frame} (hx : fr'.func.externs = fr.func.externs)
    (hs : fr'.func.sig = fr.func.sig) (hle : Valuation.Le fr.regs fr'.regs) (fn : FnRef)
    (args : List ValueId) : RR (Opt.tailArgs fr fn args) (Opt.tailArgs fr' fn args) := by
  unfold Opt.tailArgs
  rw [show fr'.func.extern? fn = fr.func.extern? fn by simp [Function.extern?, hx], hs]
  exact RR.bind (RR.refl _) fun _ _ => RR.bind (getMany_RR hle args) fun _ _ => RR.refl _

theorem ciArgs_RR {fr fr' : Frame} (hd : fr'.func.sigDecls = fr.func.sigDecls)
    (hle : Valuation.Le fr.regs fr'.regs) (sig : Nat) (callee : ValueId) (args : List ValueId) :
    RR (Opt.ciArgs fr sig callee args) (Opt.ciArgs fr' sig callee args) := by
  unfold Opt.ciArgs
  rw [hd]
  exact RR.bind (RR.refl _) fun _ _ => RR.bind (get_RR hle callee) fun _ _ =>
    RR.bind (RR.refl _) fun _ _ => RR.bind (getMany_RR hle args) fun _ _ => RR.refl _

theorem stepReturnCall_eq (env : Env) (p : Program) (s : State) (fn : FnRef) (args : List ValueId) :
    stepReturnCall env p s fn args =
      StepResult.ofRes (Opt.tailArgs s.frame fn args) fun (ext, vals) =>
        Opt.tailCont env p s ext vals := rfl

theorem continueWith_rel {env : Env} {P P' : Program} {s s' : State} (hF : FR P s.frame s'.frame)
    (hC : CR P s.callers s'.callers) (rest : List Stmt) (rs : List ValueId) (vals : List Val)
    (mem : Mem) (hsp : ∀ pl, mem.place = some pl → Chain pl.frame (names s) pl.sps) :
    StepRel env P P' (continueWith s rest rs vals mem) (continueWith s' rest rs vals mem) := by
  obtain ⟨m, hF⟩ := hF
  unfold continueWith
  cases hr : s.frame.regs.setMany rs vals with
  | none => trivial
  | some regs =>
    obtain ⟨regs', hr', hle⟩ := setMany_le hF.regs hr
    rw [hr']
    exact ⟨fun pl hp => hsp pl hp, _, rfl, .inl ⟨rfl, ⟨m, hF.update hle rest⟩, hC⟩⟩

theorem returnValues_rel {env : Env} {P P' : Program} {s s' : State} (hF : FR P s.frame s'.frame)
    (hC : CR P s.callers s'.callers) (vals : List Val) (mem : Mem)
    (hsp : ∀ pl, mem.place = some pl → Chain pl.frame (names s) pl.sps) :
    StepRel env P P' (returnValues s vals mem) (returnValues s' vals mem) := by
  obtain ⟨m, hF⟩ := hF
  obtain ⟨fr, cs, sm⟩ := s
  obtain ⟨fr', cs', sm'⟩ := s'
  unfold returnValues
  dsimp only at hF hC ⊢
  rw [hF.hdr.1, hF.hdr.2.1, hF.slots]
  apply ofRes_rel (RR.refl _)
  intro _ _
  cases hC with
  | nil => rfl
  | cons hab hrest =>
    rename_i a b as bs
    obtain ⟨c, rs⟩ := a
    obtain ⟨c', rs'⟩ := b
    obtain ⟨hrs, mc, hc⟩ := hab
    dsimp only at hrs
    subst hrs
    dsimp only
    cases hr : c.regs.setMany rs' vals with
    | none => trivial
    | some regs =>
      obtain ⟨regs', hr', hle⟩ := setMany_le hc.regs hr
      rw [hr']
      exact ⟨sps_leave hsp, _, rfl, .inl ⟨rfl, ⟨mc, hc.setRegs hle⟩, hrest⟩⟩

/-- A call (`call`, the call of a `try_call`) after its prelude. -/
theorem callCont_rel {env : Env} {P P' : Program} (hP : TailRel P P') (hk : EnvKeepsPlace env)
    {s s' : State} (hT : TR P s s') (hsp : SpsOk s) (rest : List Stmt) (rs : List ValueId)
    (ext : ExtFunc) (vals : List Val) :
    StepRel env P P' (Opt.callCont env P s rest rs ext vals) (Opt.callCont env P' s' rest rs ext vals) := by
  obtain ⟨fr', cs', sm'⟩ := s'
  obtain ⟨hm, ⟨m, hF⟩, hcs⟩ := hT
  dsimp only at hm hF hcs
  subst hm
  have hT : TR P s ⟨fr', cs', s.mem⟩ := ⟨rfl, ⟨m, hF⟩, hcs⟩
  unfold Opt.callCont
  dsimp only
  cases hlk : P.func? ext.name with
  | some c =>
    obtain ⟨g, hg, hcg⟩ := (hP.func? ext.name).1 c hlk
    simp only [hg, tp_sig hcg]
    split
    · cases he : enterFunc c vals s.mem with
      | ok p =>
        obtain ⟨fr1, mem1⟩ := p
        obtain ⟨fr1', he', hN⟩ := enterFunc_rel hcg (func?_self hlk) he
        rw [he']
        refine ⟨?_, _, rfl, hN env _ _ (.cons ⟨rfl, ⟨m, hF.update hF.regs rest⟩⟩ hT.callers)⟩
        have hfn := enterFunc_func he
        intro pl hp
        have := sps_enter he hsp pl hp
        simpa [names, hfn] using this
      | trap c => exact absurd he (enterFunc_ne_trap _ _ _ _)
      | stuck _ => trivial
    · trivial
  | none =>
    rw [(hP.func? ext.name).2 hlk]
    cases hx : env.extern ext.name with
    | none => trivial
    | some f =>
      dsimp only
      cases ho : f vals s.mem with
      | returned rvals mem' =>
        dsimp only
        split
        · refine continueWith_rel (s' := ⟨fr', cs', s.mem⟩) ⟨m, hF⟩ hT.callers rest rs rvals mem' ?_
          rw [hk ext.name f hx vals s.mem rvals mem' ho]; exact hsp
        · trivial
      | trapped c => rfl
      | stuck _ => trivial
      | outOfFuel => trivial

/-- A `call_indirect` (also of a `try_call_indirect`) after its prelude. -/
theorem ciCont_rel {env : Env} {P P' : Program} (hP : TailRel P P')
    (hnd : (P.funcs.map (·.name)).Nodup) (hk : EnvKeepsPlace env)
    {s s' : State} (hT : TR P s s') (hsp : SpsOk s) (rest : List Stmt) (rs : List ValueId)
    (sig : Nat) (d : Signature) (addr : Nat) (vals : List Val) :
    StepRel env P P' (Opt.ciCont env P s rest rs sig d addr vals)
      (Opt.ciCont env P' s' rest rs sig d addr vals) := by
  obtain ⟨fr', cs', sm'⟩ := s'
  obtain ⟨hm, ⟨m, hF⟩, hcs⟩ := hT
  dsimp only at hm hF hcs
  subst hm
  have hT : TR P s ⟨fr', cs', s.mem⟩ := ⟨rfl, ⟨m, hF⟩, hcs⟩
  unfold Opt.ciCont
  dsimp only
  cases hlk : P.funcs.find? (fun f => s.mem.symbols f.name == some addr) with
  | some c =>
    obtain ⟨g, hg, hcg⟩ := (find?_rel hP (fun n => s.mem.symbols n == some addr)).1 c hlk
    have hg' : P'.funcs.find? (fun f => s.mem.symbols f.name == some addr) = some g := hg
    simp only [hg', tp_sig hcg]
    split
    · cases he : enterFunc c vals s.mem with
      | ok p =>
        obtain ⟨fr1, mem1⟩ := p
        obtain ⟨fr1', he', hN⟩ :=
          enterFunc_rel hcg (func?_of_mem hnd (List.mem_of_find?_eq_some hlk)) he
        rw [he']
        refine ⟨?_, _, rfl, hN env _ _ (.cons ⟨rfl, ⟨m, hF.update hF.regs rest⟩⟩ hT.callers)⟩
        have hfn := enterFunc_func he
        intro pl hp
        have := sps_enter he hsp pl hp
        simpa [names, hfn] using this
      | trap c => exact absurd he (enterFunc_ne_trap _ _ _ _)
      | stuck _ => trivial
    · trivial
  | none =>
    have hg' : P'.funcs.find? (fun f => s.mem.symbols f.name == some addr) = none :=
      (find?_rel hP (fun n => s.mem.symbols n == some addr)).2 hlk
    rw [hg', Opt.callExternAt_congr hP.externNames]
    exact ofRes_rel (RR.refl _) fun ⟨rvals, mem'⟩ he =>
      continueWith_rel (s' := ⟨fr', cs', s.mem⟩) ⟨m, hF⟩ hT.callers rest rs rvals mem'
        (by rw [callExternAt_place hk he]; exact hsp)

/-- A `return_call` after its prelude, the target's terminator being the same `return_call`. -/
theorem tailCont_rel {env : Env} {P P' : Program} (hP : TailRel P P') (hk : EnvKeepsPlace env)
    {s s' : State} (hT : TR P s s') (hsp : SpsOk s) (ext : ExtFunc) (vals : List Val) :
    StepRel env P P' (Opt.tailCont env P s ext vals) (Opt.tailCont env P' s' ext vals) := by
  obtain ⟨fr', cs', sm'⟩ := s'
  obtain ⟨hm, ⟨m, hF⟩, hcs⟩ := hT
  dsimp only at hm hF hcs
  subst hm
  have hT : TR P s ⟨fr', cs', s.mem⟩ := ⟨rfl, ⟨m, hF⟩, hcs⟩
  unfold Opt.tailCont
  dsimp only
  rw [hF.slots]
  cases hlk : P.func? ext.name with
  | some c =>
    obtain ⟨g, hg, hcg⟩ := (hP.func? ext.name).1 c hlk
    simp only [hg, tp_sig hcg]
    split
    · cases he : enterFunc c vals ((s.mem.free (s.frame.slots.map (·.2))).leave) with
      | ok p =>
        obtain ⟨fr1, mem1⟩ := p
        obtain ⟨fr1', he', hN⟩ := enterFunc_rel hcg (func?_self hlk) he
        rw [he']
        refine ⟨?_, _, rfl, hN env _ _ hT.callers⟩
        have hfn := enterFunc_func he
        intro pl hp
        have := sps_enter he (sps_leave hsp) pl hp
        simpa [names, hfn] using this
      | trap c => exact absurd he (enterFunc_ne_trap _ _ _ _)
      | stuck _ => trivial
    · trivial
  | none =>
    rw [(hP.func? ext.name).2 hlk]
    cases hx : env.extern ext.name with
    | none => trivial
    | some f =>
      dsimp only
      cases ho : f vals s.mem with
      | returned rvals mem' =>
        refine returnValues_rel (s' := ⟨fr', cs', s.mem⟩) ⟨m, hF⟩ hT.callers rvals mem' ?_
        rw [hk ext.name f hx vals s.mem rvals mem' ho]; exact hsp
      | trapped c => rfl
      | stuck _ => trivial
      | outOfFuel => trivial

/-- Entering a block (a branch) keeps the relation. -/
theorem jump_rel {env : Env} {P P' : Program} {s s' : State} {m : Bool} (hT : TR P s s')
    (hF : FRm P m s.frame s'.frame) (hsp : SpsOk s) (bc : BlockCall) :
    StepRel env P P' (StepResult.ofRes (enterBlock s.frame bc) fun fr => .next { s with frame := fr })
      (StepResult.ofRes (enterBlock s'.frame bc) fun fr => .next { s' with frame := fr }) := by
  cases he : enterBlock s.frame bc with
  | ok fr1 =>
    obtain ⟨fr1', he', h1⟩ := enterBlock_rel hF he
    rw [he']
    obtain ⟨_, _, _, _, _, _, _, hfr⟩ := Opt.enterBlock_ok he
    have hfn : fr1.func = s.frame.func := by rw [hfr]
    refine ⟨?_, _, rfl, .inl ⟨hT.mem, ⟨m, h1⟩, hT.callers⟩⟩
    intro pl hp
    have := hsp pl hp
    simpa [names, hfn] using this
  | trap c => exact absurd he (enterBlock_ne_trap _ _ _)
  | stuck _ => trivial

/-- **A self `return_call` and the loop's `jump`**: the source re-enters the function (with
the memory it starts from, `selfTail_mem`), the target jumps to the first block; the frames are
related again. -/
theorem selfTail_rel {env : Env} {P P' : Program} {s s' : State} (hT : TR P s s')
    (hF : FRm P true s.frame s'.frame) (hsp : SpsOk s) {fn : FnRef} {args : List ValueId}
    (hst : selfTail s.frame.func fn = true) :
    StepRel env P P' (stepReturnCall env P s fn args)
      (stepTerm env P' s' (.jump ⟨b0id s.frame.func, args⟩)) := by
  obtain ⟨fr, cs, sm'⟩ := s
  obtain ⟨fr', cs', sm'⟩ := s'
  obtain ⟨hm, -, hcs⟩ := hT
  dsimp only at hm hcs hF hst ⊢
  subst hm
  have hel := hF.elig rfl
  obtain ⟨hs, hnt, b0, bs, hb, hpar⟩ := eligB_spec hel
  have hsl : fr.slots = [] := hF.noSlots rfl
  have hself : P.func? fr.func.name = some fr.func := hF.self rfl
  rw [stepReturnCall_eq]
  simp only [selfTail] at hst
  cases hext : fr.func.extern? fn with
  | none => simp [hext] at hst
  | some ext =>
  simp only [hext, Bool.and_eq_true, beq_iff_eq] at hst
  obtain ⟨⟨hn, hp⟩, hr⟩ := hst
  cases hga : fr.getMany args with
  | trap c => exact absurd hga (getMany_ne_trap _ _ _)
  | stuck _ => simp [Opt.tailArgs, hext, hga]; trivial
  | ok vals =>
  by_cases hty : vals.map (·.ty) = AbiParam.tys ext.sig.params
  rotate_left
  · have hf : (vals.map (·.ty) == AbiParam.tys ext.sig.params) = false := by simpa using hty
    simp [Opt.tailArgs, hext, hga, checkTys, hf]; trivial
  have hta : Opt.tailArgs fr fn args = .ok (ext, vals) := by
    simp [Opt.tailArgs, hext, hga, checkTys, hty, hr]
  rw [hta]
  simp only [StepResult.ofRes_ok]
  -- the source re-enters the function
  have h1 : vals.map (·.ty) = AbiParam.tys fr.func.sig.params := hty.trans hp
  have h2 : vals.map (·.ty) = b0.params.map (·.2) := h1.trans hpar.symm
  have hlen : (b0.params.map (·.1)).length = vals.length := by
    have := congrArg List.length h2; simpa using this.symm
  obtain ⟨rP, hrP⟩ := setMany_some Regs.empty _ vals hlen
  have hent : fr.func.entry? = some b0 := by simp [Function.entry?, hb]
  have hmem : enterSlots fr.func ((sm'.free (fr.slots.map (·.2))).leave) = ([], sm') := by
    rw [hsl]; exact selfTail_mem hs (ns := cs.map (fun c : Frame × List ValueId => c.1.func.name)) (fun pl hp => hsp pl hp)
  have hsrc : Opt.tailCont env P ⟨fr, cs, sm'⟩ ext vals =
      .next ⟨⟨fr.func, rP, [], b0.body, b0.term⟩, cs, sm'⟩ := by
    simp only [Opt.tailCont, hn, hself, hp, hr, beq_self_eq_true, Bool.and_self, if_true]
    rw [Opt.enterFunc_of hent h1 h2 hrP, hmem]
    rfl
  rw [hsrc]
  -- the target jumps to the first block
  have hbl : fr.func.block? b0.id = some b0 := by simp [Function.block?, hb]
  have hlb := loop_block? hel hbl
  rw [b0id_eq hb] at hlb ⊢
  have hfunc : fr'.func = loop fr.func := by rw [hF.func]; rfl
  obtain ⟨r2, hr2, hle⟩ := setMany_le (le_empty fr'.regs) hrP
  have hga' := getMany_le hF.regs hga
  have htgt : enterBlock fr' ⟨b0.id, args⟩ =
      .ok ⟨fr'.func, r2, fr'.slots, b0.body, (blockT fr.func b0.id b0).term⟩ := by
    simp only [enterBlock, hfunc, hlb, Res.ofOption_some, Res.ok_bind, hga', checkTys, blockT, ← h2,
      beq_self_eq_true, Res.check_true, hr2, Res.pure_eq]
  simp only [stepTerm, htgt, StepResult.ofRes_ok]
  refine ⟨fun pl hp => hsp pl hp, _, rfl, .inl ⟨rfl, ⟨true, ?_⟩, hcs⟩⟩
  exact {
    func := hfunc
    regs := hle
    slots := by rw [hF.slots, hsl]
    body := rfl
    term := by simp [blockT, b0id_eq hb]
    elig := fun _ => hel
    noTry := fun _ => hnt b0 (by rw [hb]; exact List.mem_cons_self ..)
    self := fun _ => hself
    noSlots := fun _ => rfl }

/-- **One source step is matched** (module doc). -/
theorem step_rel {env : Env} {P P' : Program} (hP : TailRel P P')
    (hnd : (P.funcs.map (·.name)).Nodup) (hk : EnvKeepsPlace env) {s s' : State}
    (hT : TR P s s') (hsp : SpsOk s) : StepRel env P P' (step env P s) (step env P' s') := by
  obtain ⟨m, hF⟩ := hT.frame
  have hT' := hT
  obtain ⟨hmem, -, hcs⟩ := hT'
  cases hb : s.frame.body with
  | cons st rest =>
    have hb' : s'.frame.body = st :: rest := hF.body.trans hb
    obtain ⟨results, inst⟩ := st
    by_cases hc : ∃ fn args, inst = .call fn args
    · obtain ⟨fn, args, rfl⟩ := hc
      rw [step_call env P s rest results fn args hb, step_call env P' s' rest results fn args hb',
        Opt.stepCall_eq, Opt.stepCall_eq]
      exact ofRes_rel (callArgs_RR hF.hdr.2.2.2.2.1 hF.regs fn args) fun ⟨ext, vals⟩ _ =>
        callCont_rel hP hk hT hsp rest results ext vals
    by_cases hci : ∃ sig callee args, inst = .callIndirect sig callee args
    · obtain ⟨sig, callee, args, rfl⟩ := hci
      have e1 : step env P s = stepCallIndirect env P s rest results sig callee args := by
        simp [step, hb]
      have e2 : step env P' s' = stepCallIndirect env P' s' rest results sig callee args := by
        simp [step, hb']
      rw [e1, e2, Opt.stepCallIndirect_eq, Opt.stepCallIndirect_eq]
      exact ofRes_rel (ciArgs_RR hF.hdr.2.2.2.2.2 hF.regs sig callee args) fun ⟨d, a, vals⟩ _ =>
        ciCont_rel hP hnd hk hT hsp rest results sig d a vals
    have hc' : ∀ fn args, inst ≠ .call fn args := fun fn args h => hc ⟨fn, args, h⟩
    have hci' : ∀ sig callee args, inst ≠ .callIndirect sig callee args :=
      fun sig callee args h => hci ⟨sig, callee, args, h⟩
    rw [step_inst env P s ⟨results, inst⟩ rest hb hc' hci',
      step_inst env P' s' ⟨results, inst⟩ rest hb' hc' hci', hmem]
    have hrr : RR (evalInst s.frame s.mem inst) (evalInst s'.frame s.mem inst) := by
      have hh := hF.hdr
      refine ⟨fun a ha => ?_, fun c hc => ?_⟩
      · rw [Opt.evalInst_mono hh.2.2.2.1 hh.2.2.2.2.1 hF.slots hF.regs
          (fun m h => by rw [ha] at h; cases h)]; exact ha
      · rw [Opt.evalInst_mono hh.2.2.2.1 hh.2.2.2.2.1 hF.slots hF.regs
          (fun m h => by rw [hc] at h; cases h)]; exact hc
    exact ofRes_rel hrr fun ⟨vals, mem⟩ he =>
      continueWith_rel ⟨m, hF⟩ hcs rest results vals mem
        (by rw [(evalInst_place he).1]; exact hsp)
  | nil =>
    have hb' : s'.frame.body = [] := hF.body.trans hb
    rw [step_term env P s hb, step_term env P' s' hb', hF.term]
    cases ht : s.frame.term with
    | jump d =>
      have : (if m = true then termT s.frame.func (b0id s.frame.func) (.jump d) else .jump d) =
          .jump d := by cases m <;> rfl
      rw [this]
      exact jump_rel hT hF hsp d
    | brif c t e =>
      have : (if m = true then termT s.frame.func (b0id s.frame.func) (.brif c t e) else .brif c t e) =
          .brif c t e := by cases m <;> rfl
      rw [this]
      simp only [stepTerm]
      exact ofRes_rel (get_RR hF.regs c) fun cv _ => jump_rel hT hF hsp _
    | brTable x dflt table =>
      have : (if m = true then termT s.frame.func (b0id s.frame.func) (.brTable x dflt table)
          else .brTable x dflt table) = .brTable x dflt table := by cases m <;> rfl
      rw [this]
      simp only [stepTerm]
      exact ofRes_rel (get_RR hF.regs x) fun xv _ => jump_rel hT hF hsp _
    | ret xs =>
      have : (if m = true then termT s.frame.func (b0id s.frame.func) (.ret xs) else .ret xs) =
          .ret xs := by cases m <;> rfl
      rw [this]
      simp only [stepTerm]
      rw [hmem]
      exact ofRes_rel (getMany_RR hF.regs xs) fun vals _ =>
        returnValues_rel ⟨m, hF⟩ hcs vals s.mem hsp
    | returnCall fn args =>
      have hgen : StepRel env P P' (stepTerm env P s (.returnCall fn args))
          (stepTerm env P' s' (.returnCall fn args)) := by
        simp only [stepTerm]
        rw [stepReturnCall_eq, stepReturnCall_eq]
        exact ofRes_rel (tailArgs_RR hF.hdr.2.2.2.2.1 hF.hdr.2.1 hF.regs fn args)
          fun ⟨ext, vals⟩ _ => tailCont_rel hP hk hT hsp ext vals
      cases m with
      | false => exact hgen
      | true =>
        by_cases hst : selfTail s.frame.func fn = true
        · simp only [if_true, termT, hst]
          exact selfTail_rel hT hF hsp hst
        · simp only [if_true, termT, hst]
          exact hgen
    | trap c =>
      have : (if m = true then termT s.frame.func (b0id s.frame.func) (.trap c) else .trap c) =
          .trap c := by cases m <;> rfl
      rw [this]
      rfl
    | tryCall fn args et =>
      cases m with
      | true => have := hF.noTry rfl; rw [ht] at this; cases this
      | false =>
        simp only [Bool.false_eq_true, if_false, stepTerm]
        rw [Opt.stepTryCall_eq, Opt.stepTryCall_eq]
        have hfn : s'.frame.func = s.frame.func := hF.func
        have htc : Opt.tcArgs s'.frame fn et = Opt.tcArgs s.frame fn et := by
          unfold Opt.tcArgs; rw [hfn]
        rw [htc]
        refine ofRes_rel (RR.refl _) fun ⟨n, base, bc⟩ _ =>
          ofRes_rel (callArgs_RR hF.hdr.2.2.2.2.1 hF.regs fn args) fun ⟨ext, vals⟩ _ => ?_
        have hJ : FRm P false (Opt.jumpFrame s.frame bc) (Opt.jumpFrame s'.frame bc) := {
          func := hF.func, regs := hF.regs, slots := hF.slots, body := rfl, term := rfl,
          elig := fun h => (by cases h), noTry := fun h => (by cases h),
          self := fun h => (by cases h), noSlots := fun h => (by cases h) }
        exact callCont_rel (s := { s with frame := Opt.jumpFrame s.frame bc })
          (s' := { s' with frame := Opt.jumpFrame s'.frame bc }) hP hk ⟨hmem, ⟨false, hJ⟩, hcs⟩
          (fun pl hp => hsp pl hp) [] _ ext vals
    | tryCallIndirect callee args et =>
      cases m with
      | true => have := hF.noTry rfl; rw [ht] at this; cases this
      | false =>
        simp only [Bool.false_eq_true, if_false, stepTerm]
        rw [Opt.stepTryCallIndirect_eq, Opt.stepTryCallIndirect_eq]
        have hfn : s'.frame.func = s.frame.func := hF.func
        have htc : Opt.ticArgs s'.frame et = Opt.ticArgs s.frame et := by
          unfold Opt.ticArgs; rw [hfn]
        rw [htc]
        refine ofRes_rel (RR.refl _) fun ⟨n, base, bc⟩ _ =>
          ofRes_rel (ciArgs_RR hF.hdr.2.2.2.2.2 hF.regs et.sig callee args) fun ⟨d, a, vals⟩ _ => ?_
        have hJ : FRm P false (Opt.jumpFrame s.frame bc) (Opt.jumpFrame s'.frame bc) := {
          func := hF.func, regs := hF.regs, slots := hF.slots, body := rfl, term := rfl,
          elig := fun h => (by cases h), noTry := fun h => (by cases h),
          self := fun h => (by cases h), noSlots := fun h => (by cases h) }
        exact ciCont_rel (s := { s with frame := Opt.jumpFrame s.frame bc })
          (s' := { s' with frame := Opt.jumpFrame s'.frame bc }) hP hnd hk ⟨hmem, ⟨false, hJ⟩, hcs⟩
          (fun pl hp => hsp pl hp) [] _ et.sig d a vals

/-! ## Runs -/

/-- **Runs are matched**: the target's fuel for a source run of `k` steps; when the source run
returns or traps, every state the target run reaches has as many callers as a state the source
run reaches. -/
theorem run_rel {env : Env} {P P' : Program} (hP : TailRel P P')
    (hnd : (P.funcs.map (·.name)).Nodup) (hk : EnvKeepsPlace env) :
    ∀ (k : Nat) (s s' : State), TR P s s' → SpsOk s →
      ∃ n, (∀ v cm, runLoop env P k s = .returned v cm → runLoop env P' n s' = .returned v cm) ∧
        (∀ c, runLoop env P k s = .trapped c → runLoop env P' n s' = .trapped c) ∧
        (Opt.Final (runLoop env P k s) → ∀ u', Clif.Reaches env P' s' u' →
          ∃ u, Clif.Reaches env P s u ∧ u'.callers.length = u.callers.length)
  | 0, _, _, _, _ => ⟨0, by intro v cm h; simp at h, by intro c h; simp at h,
      by intro h; simp [Opt.Final] at h⟩
  | k + 1, s, s', hT, hsp => by
    have hS := step_rel (env := env) hP hnd hk hT hsp
    cases hs : step env P s with
    | next t =>
      rw [hs] at hS
      obtain ⟨hspt, t1', h1, hN⟩ := hS
      rcases hN with hT1 | ⟨t2', h2, hc2, hT2⟩
      · obtain ⟨n, r1, r2, r3⟩ := run_rel hP hnd hk k t t1' hT1 hspt
        refine ⟨n + 1, fun v cm h => ?_, fun c h => ?_, fun hf u' hu => ?_⟩
        · rw [runLoop_succ, hs] at h; rw [runLoop_succ, h1]; exact r1 v cm h
        · rw [runLoop_succ, hs] at h; rw [runLoop_succ, h1]; exact r2 c h
        · rw [runLoop_succ, hs] at hf
          cases hu with
          | refl => exact ⟨s, .refl _, hT.callers.length⟩
          | next hx hr =>
            rw [h1] at hx; cases hx
            obtain ⟨u, hu1, hu2⟩ := r3 hf u' hr
            exact ⟨u, .next hs hu1, hu2⟩
      · obtain ⟨n, r1, r2, r3⟩ := run_rel hP hnd hk k t t2' hT2 hspt
        refine ⟨n + 2, fun v cm h => ?_, fun c h => ?_, fun hf u' hu => ?_⟩
        · rw [runLoop_succ, hs] at h; rw [runLoop_succ, h1]
          show runLoop env P' (n + 1) t1' = _
          rw [runLoop_succ, h2]; exact r1 v cm h
        · rw [runLoop_succ, hs] at h; rw [runLoop_succ, h1]
          show runLoop env P' (n + 1) t1' = _
          rw [runLoop_succ, h2]; exact r2 c h
        · rw [runLoop_succ, hs] at hf
          cases hu with
          | refl => exact ⟨s, .refl _, hT.callers.length⟩
          | next hx hr =>
            rw [h1] at hx; cases hx
            cases hr with
            | refl => exact ⟨t, .next hs (.refl _), by rw [← hc2]; exact hT2.callers.length⟩
            | next hx2 hr2 =>
              rw [h2] at hx2; cases hx2
              obtain ⟨u, hu1, hu2⟩ := r3 hf u' hr2
              exact ⟨u, .next hs hu1, hu2⟩
    | done v m =>
      rw [hs] at hS
      refine ⟨1, fun v' cm h => ?_, fun c h => ?_, fun _ u' hu => ?_⟩
      · rw [runLoop_succ, hs] at h; rw [runLoop_succ, hS]; exact h
      · rw [runLoop_succ, hs] at h; cases h
      · cases hu with
        | refl => exact ⟨s, .refl _, hT.callers.length⟩
        | next hx _ => rw [hS] at hx; cases hx
    | trapped c =>
      rw [hs] at hS
      refine ⟨1, fun v' cm h => ?_, fun c' h => ?_, fun _ u' hu => ?_⟩
      · rw [runLoop_succ, hs] at h; cases h
      · rw [runLoop_succ, hs] at h; rw [runLoop_succ, hS]; exact h
      · cases hu with
        | refl => exact ⟨s, .refl _, hT.callers.length⟩
        | next hx _ => rw [hS] at hx; cases hx
    | stuck _ =>
      refine ⟨0, ?_, ?_, ?_⟩
      · intro v cm h; rw [runLoop_succ, hs] at h; cases h
      · intro c h; rw [runLoop_succ, hs] at h; cases h
      · intro hf; rw [runLoop_succ, hs] at hf; cases hf

/-! ## Entries -/

/-- Related entries: the same, or after the target's new entry block's `jump`. -/
theorem entry_rel {env : Env} {P P' : Program} {n : String} {f g : Function}
    (hf : P.func? n = some f) (hfg : TP f g) {args : List Val} {cs cs' : State}
    (hcs : E2E.ClifEntry f args cs) (hcs' : E2E.ClifEntry g args cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem) :
    TR P cs cs' ∨ ∃ cs2, step env P' cs' = .next cs2 ∧ cs2.callers = cs'.callers ∧ TR P cs cs2 := by
  have hcl : CR P cs.callers cs'.callers := by rw [hcs.callers, hcs'.callers]; exact .nil
  obtain ⟨b, hb, hbody, hterm, hpty, hregs⟩ := hcs.entry
  have hsame : g = f → TR P cs cs' := by
    intro hgf
    subst hgf
    obtain ⟨b', hb', hbody', hterm', -, hregs'⟩ := hcs'.entry
    rw [hb] at hb'; cases hb'
    rw [hregs] at hregs'
    have hR : cs.frame.regs = cs'.frame.regs := Option.some.inj hregs'
    exact ⟨hmem, ⟨false, {
      func := by simp only [Bool.false_eq_true, if_false]; rw [hcs'.func, hcs.func]
      regs := by rw [← hR]; exact le_refl' _
      slots := hsl
      body := by rw [hbody', hbody]
      term := by simp only [Bool.false_eq_true, if_false]; rw [hterm', hterm]
      elig := fun h => (by cases h)
      noTry := fun h => (by cases h)
      self := fun h => (by cases h)
      noSlots := fun h => (by cases h) }⟩, hcl⟩
  rcases hfg with rfl | rfl
  · exact .inl (hsame rfl)
  cases hel : eligB f with
  | false => exact .inl (hsame (loop_of_not hel))
  | true =>
  right
  obtain ⟨hs, hnt, b0, bs, hb0, hpar⟩ := eligB_spec hel
  have hbb : b = b0 := by simp [Function.entry?, hb0] at hb; exact hb.symm
  subst hbb
  obtain ⟨b', hb', hbody', hterm', hpty', hregs'⟩ := hcs'.entry
  rw [loop_entry hb0 hel] at hb'; cases hb'
  have hbl : f.block? b.id = some b := by simp [Function.block?, hb0]
  have hlb := loop_block? hel hbl
  rw [b0id_eq hb0] at hlb
  obtain ⟨r2, hr2, hle⟩ := setMany_le (le_empty cs'.frame.regs) hregs
  have hgm : cs'.frame.getMany ((freshParams f.freshValue b.params).map (·.1)) = .ok args :=
    getMany_setMany (freshParams_nodup _ _) (by simpa only [entryBlock] using hregs') _ rfl
  have hfunc : cs'.frame.func = loop f := hcs'.func
  have hcslots : cs.frame.slots = [] := by
    have := hcs.slotIds; rw [hs] at this; simpa using this
  refine ⟨⟨⟨loop f, r2, cs'.frame.slots, b.body, (blockT f b.id b).term⟩, cs'.callers, cs'.mem⟩,
    ?_, rfl, ⟨hmem, ⟨true, ?_⟩, hcl⟩⟩
  · have hb'' : cs'.frame.body = [] := by rw [hbody']; rfl
    rw [step_term env P' cs' hb'', hterm']
    simp only [entryBlock, stepTerm, enterBlock, hfunc, hlb, Res.ofOption_some, Res.ok_bind, hgm,
      checkTys, blockT, ← hpty, beq_self_eq_true, Res.check_true, hr2, Res.pure_eq,
      StepResult.ofRes_ok]
  · exact {
      func := by rw [hcs.func]; rfl
      regs := hle
      slots := by rw [hsl]
      body := by rw [hbody]
      term := by rw [hterm, hcs.func]; simp [blockT, b0id_eq hb0]
      elig := fun _ => by rw [hcs.func]; exact hel
      noTry := fun _ => by rw [hterm]; exact hnt b (by rw [hb0]; exact List.mem_cons_self ..)
      self := fun _ => by rw [hcs.func]; exact func?_self hf
      noSlots := fun _ => hcslots }

/-- The oracle stack of an entry without the oracle is consistent. -/
theorem spsOk_none {cs : State} (h : cs.mem.place = none) : SpsOk cs := fun pl hp => by
  rw [h] at hp; cases hp

/-- The oracle stack of an entry (no callers) of `f` is consistent when its top is what entering
`f` from the stack below pushes. -/
theorem spsOk_entry {f : Function} {cs : State} (hc : cs.callers = []) (hf : cs.frame.func = f)
    (h : ∀ pl, cs.mem.place = some pl → ∃ xs, pl.sps = spOf pl.frame f.name xs :: xs) :
    SpsOk cs := fun pl hp => by
  obtain ⟨xs, hx⟩ := h pl hp
  simp only [names, hc, hf, List.map_nil, hx, Chain, and_true]

/-- **Self tail calls as loops refine the program** (module doc): for `TailRel P P'` (distinct
names in `P`, externs keeping the slot-placement oracle), the run of `P'` from the entry `cs'` of
the counterpart `g` of `P`'s function `f` named `n` (same arguments, slots and memory as the
entry `cs` of `f`, whose oracle stack is consistent) returns what the run of `P` from `cs`
returns and traps where it traps; when `P`'s run returns or traps, `P'`'s run has no larger call
depth. -/
theorem TailRel.refines {B : Env} {P P' : Program} (hP : TailRel P P')
    (hnd : (P.funcs.map (·.name)).Nodup) (hk : EnvKeepsPlace B) {n : String} {f g : Function}
    (hf : P.func? n = some f) (hg : P'.func? n = some g) {args : List Val} {cs cs' : State}
    (hcs : E2E.ClifEntry f args cs) (hcs' : E2E.ClifEntry g args cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem) (hsp : SpsOk cs)
    (k : Nat) :
    ∃ m, (∀ v cm, runLoop B P k cs = .returned v cm → runLoop B P' m cs' = .returned v cm) ∧
      (∀ c, runLoop B P k cs = .trapped c → runLoop B P' m cs' = .trapped c) ∧
      (Opt.Final (runLoop B P k cs) → ∀ d, Clif.DepthLe B P d cs → Clif.DepthLe B P' d cs') := by
  obtain ⟨g', hg', hfg⟩ := (hP.func? n).1 f hf
  rw [hg] at hg'; cases hg'
  rcases entry_rel (env := B) hf hfg hcs hcs' hsl hmem with hT | ⟨cs2, h1, hc2, hT⟩
  · obtain ⟨m, r1, r2, r3⟩ := run_rel hP hnd hk k cs cs' hT hsp
    refine ⟨m, r1, r2, fun hfin d hd u' hu => ?_⟩
    obtain ⟨u, hu1, hu2⟩ := r3 hfin u' hu
    rw [hu2]; exact hd u hu1
  · obtain ⟨m, r1, r2, r3⟩ := run_rel hP hnd hk k cs cs2 hT hsp
    refine ⟨m + 1, fun v cm h => ?_, fun c h => ?_, fun hfin d hd u' hu => ?_⟩
    · rw [runLoop_succ, h1]; exact r1 v cm h
    · rw [runLoop_succ, h1]; exact r2 c h
    · cases hu with
      | refl => rw [hcs'.callers]; exact Nat.zero_le _
      | next hx hr =>
        rw [h1] at hx; cases hx
        obtain ⟨u, hu1, hu2⟩ := r3 hfin u' hr
        rw [hu2]; exact hd u hu1

end Opt.TailLoop
