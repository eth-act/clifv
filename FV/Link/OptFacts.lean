import FV.Link.OptCompile
import FV.E2E.OptX

/-! # The optimised input of the executable compiler: what it keeps

`LinkSpec.opt` (`FV/Link/OptCompile.lean`) replaces each function of the input by its optimised
function or keeps it (`FnInput.opt_func`). Pointwise, the optimised program's function simulates
the input program's (`Opt.FunSimX`, `call_indirect` and `try_call` included) and keeps its shape
(`E2E.ShapeFacts`), so:

* the whole-program run of the input program from an entry is refined by the optimised
  program's run from the corresponding entry (`OptRel.refines`), and when the input program's run
  returns or traps, the optimised run's call depth is bounded by the input run's (`DepthLe`);
* the facts of the linked system the source-domain context reads (`names`, `free`, `declSig`,
  `indScope`, `ProgCtx` via `srcCtx`) transfer from the optimised program back to the input
  program (`OptRel.nodup`, `OptRel.free`, `OptRel.declSig`, `OptRel.indScope`);
* an entry of an optimised function gives an entry of the input function with the same
  registers, slots and memory, related to it (`OptRel.entry`).
-/

namespace Link

open E2E E2E.LinkCheck

/-- What `FnInput.opt` does to the function. -/
theorem _root_.E2E.LinkCheck.FnInput.opt_func (fi : FnInput) :
    fi.opt.func = Opt.optimizeExe fi.func Opt.exeConfig ∨ fi.opt.func = fi.func := by
  unfold FnInput.opt
  dsimp only
  split
  · exact .inr rfl
  · split
    · rename_i h; exact .inl (of_decide_eq_true h)
    · exact .inr rfl

/-- The optimised function and the function: a simulation keeping the shape. -/
def OptPair (f g : Clif.Function) : Prop := Opt.FunSimX f g ∧ ShapeFacts f g

theorem _root_.E2E.LinkCheck.FnInput.opt_pair (fi : FnInput) : OptPair fi.func fi.opt.func := by
  rcases fi.opt_func with h | h <;> rw [h]
  · exact ⟨Opt.optimizeExe_simX _ Opt.simplifyPassSimX_exe _, optimizeExe_shape _ _⟩
  · exact ⟨Opt.FunSimX.refl _, ShapeFacts.refl _⟩

/-- Two programs with pointwise `OptPair` functions. -/
def OptRel (P P' : Clif.Program) : Prop := Opt.Pw2 OptPair P.funcs P'.funcs

theorem LinkSpec.optRel (S : LinkSpec) : OptRel S.input.prog S.opt.input.prog := by
  show Opt.Pw2 OptPair (S.funcs.map FnInput.func) ((S.funcs.map FnInput.opt).map FnInput.func)
  rw [List.map_map]
  induction S.funcs with
  | nil => exact .nil
  | cons fi fs ih => exact .cons fi.opt_pair ih

theorem linkFree_of {g : Clif.Function} (hg : Clif.LinkFree g) : Opt.retCallFreeB g = true := by
  simp only [Opt.retCallFreeB, List.all_eq_true]
  intro b hb
  cases ht : b.term with
  | returnCall fn args => exact absurd ht (hg b hb fn args)
  | _ => rfl

theorem indFree_of {g : Clif.Function} (hg : Clif.IndFree g) : Opt.indCallFreeB g = true := by
  simp only [Opt.indCallFreeB, List.all_eq_true, Bool.and_eq_true]
  intro b hb
  refine ⟨fun st hst => ?_, ?_⟩
  · cases hi : st.inst with
    | callIndirect sig callee args => exact absurd hi ((hg b hb).1 st hst sig callee args)
    | _ => rfl
  · cases ht : b.term with
    | tryCallIndirect c args et => exact absurd ht ((hg b hb).2 c args et)
    | _ => rfl

namespace OptRel

variable {P P' : Clif.Program} (h : OptRel P P')
include h

theorem funsSim : Opt.FunsSimX P.funcs P'.funcs := by
  have : ∀ {fs gs : List Clif.Function}, Opt.Pw2 OptPair fs gs → Opt.FunsSimX fs gs := by
    intro fs gs hp
    induction hp with
    | nil => exact .nil
    | cons hq _ ih => exact .cons hq.1 ih
  exact this h

theorem names : P'.funcs.map (·.name) = P.funcs.map (·.name) := by
  have : ∀ {fs gs : List Clif.Function}, Opt.Pw2 OptPair fs gs →
      gs.map (·.name) = fs.map (·.name) := by
    intro fs gs hp
    induction hp with
    | nil => rfl
    | cons hq _ ih => simp only [List.map_cons, hq.2.name, ih]
  exact this h

theorem externNames : P'.externNames = P.externNames := by
  unfold Clif.Program.externNames
  exact h.funsSim.externNames

/-- Every function of `P` has its counterpart in `P'`. -/
theorem mem {f : Clif.Function} (hf : f ∈ P.funcs) : ∃ g ∈ P'.funcs, OptPair f g := by
  have : ∀ {fs gs : List Clif.Function}, Opt.Pw2 OptPair fs gs → f ∈ fs →
      ∃ g ∈ gs, OptPair f g := by
    intro fs gs hp hm
    induction hp with
    | nil => cases hm
    | @cons x y xs ys hq _ ih =>
      rcases List.mem_cons.1 hm with rfl | hm
      · exact ⟨y, by simp, hq⟩
      · obtain ⟨g, hg, hr⟩ := ih hm
        exact ⟨g, by simp [hg], hr⟩
  exact this h hf

/-- Lookup by name finds counterparts. -/
theorem func? (n : String) :
    (∀ f, P.func? n = some f → ∃ g, P'.func? n = some g ∧ OptPair f g) ∧
      (P.func? n = none → P'.func? n = none) := by
  have : ∀ {fs gs : List Clif.Function}, Opt.Pw2 OptPair fs gs →
      (∀ f, fs.find? (·.name == n) = some f → ∃ g, gs.find? (·.name == n) = some g ∧ OptPair f g) ∧
      (fs.find? (·.name == n) = none → gs.find? (·.name == n) = none) := by
    intro fs gs hp
    induction hp with
    | nil => simp
    | @cons f g fs gs hq _ ih =>
      simp only [List.find?_cons, hq.2.name]
      split
      · exact ⟨fun f' hf => by cases hf; exact ⟨g, rfl, hq⟩, fun h => (by cases h)⟩
      · exact ih
  exact this h

theorem func?_none_iff (n : String) : P'.func? n = none ↔ P.func? n = none := by
  constructor
  · intro h'
    cases hp : P.func? n with
    | none => rfl
    | some f =>
      obtain ⟨g, hg, -⟩ := (h.func? n).1 f hp
      rw [hg] at h'; cases h'
  · exact (h.func? n).2

theorem nodup (hnd : (P'.funcs.map (·.name)).Nodup) : (P.funcs.map (·.name)).Nodup := by
  rw [← h.names]; exact hnd

theorem free (hfree : ∀ g ∈ P'.funcs, Clif.LinkFree g) : ∀ f ∈ P.funcs, Clif.LinkFree f := by
  intro f hf
  obtain ⟨g, hg, hp⟩ := h.mem hf
  exact linkFreeB_sound (hp.2.retCall (linkFree_of (hfree g hg)))

theorem declSig (hdecl : ∀ g ∈ P'.funcs, ∀ e ∈ g.externs.map (·.2), ∀ h',
      P'.func? e.name = some h' → e.sig = h'.sig) :
    ∀ f ∈ P.funcs, ∀ e ∈ f.externs.map (·.2), ∀ h', P.func? e.name = some h' → e.sig = h'.sig := by
  intro f hf e he h' hh
  obtain ⟨g, hg, hp⟩ := h.mem hf
  obtain ⟨g', hg', hp'⟩ := (h.func? e.name).1 h' hh
  rw [← hp'.2.sig]
  exact hdecl g hg e (by rw [hp.2.externs]; exact he) g' hg'

theorem indScope_iff {B : Clif.Env} {syms : String → Option Nat} :
    Clif.IndScope P' B syms → Clif.IndScope P B syms := by
  intro hI
  refine ⟨hI.keep, ?_, ?_⟩
  · rw [← h.names]; exact hI.inj
  · intro a ha b hb x hxa hxb hpa hpb
    have hn : P.names = P'.names := by
      simp only [Clif.Program.names, h.names, h.externNames]
    rw [hn] at ha hb
    exact hI.alias a ha b hb x hxa hxb ((h.func?_none_iff a).2 hpa) ((h.func?_none_iff b).2 hpb)

theorem indScope {B : Clif.Env} {syms : String → Option Nat}
    (hind : ∀ g ∈ P'.funcs, ¬ Clif.IndFree g → Clif.IndScope P' B syms) :
    ∀ f ∈ P.funcs, ¬ Clif.IndFree f → Clif.IndScope P B syms := by
  intro f hf hnf
  obtain ⟨g, hg, hp⟩ := h.mem hf
  refine h.indScope_iff (hind g hg fun hgf => hnf (indFreeB_sound ?_))
  exact hp.2.indCall (indFree_of hgf)

/-- **An entry of an optimised function gives an entry of the input function**, with the same
registers, slots and memory, related to it. -/
theorem entry {n : String} {f g : Clif.Function} (hf : P.func? n = some f)
    (hg : P'.func? n = some g) {args : List Clif.Val} {cs' : Clif.State}
    (hcs' : ClifEntry g args cs') :
    ∃ cs, ClifEntry f args cs ∧ cs.frame.regs = cs'.frame.regs ∧
      cs.frame.slots = cs'.frame.slots ∧ cs.mem = cs'.mem ∧
      (∃ b, f.entry? = some b ∧ cs.frame.body = b.body ∧ cs.frame.term = b.term) ∧
      Opt.SRX cs'.mem.symbols cs cs' := by
  obtain ⟨g', hg', hp⟩ := (h.func? n).1 f hf
  rw [hg] at hg'; cases hg'
  obtain ⟨b', hb', hbody', hterm', hty', hregs'⟩ := hcs'.entry
  have hfb : f.entry? ≠ none := by
    intro hn
    have : f.blocks = [] := by simpa [Clif.Function.entry?] using hn
    have := hp.2.blocksNil this
    simp [Clif.Function.entry?, this] at hb'
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 hfb
  obtain ⟨R, hR, hent⟩ := hp.1.sim cs'.mem.symbols
  obtain ⟨b'', hb'', hpar, hrel⟩ := hent b hb
  rw [hb'] at hb''; cases hb''
  refine ⟨⟨⟨f, cs'.frame.regs, cs'.frame.slots, b.body, b.term⟩, [], cs'.mem⟩,
    ⟨rfl, rfl, by rw [← hp.1.sig]; exact hcs'.sig, ⟨b, hb, rfl, rfl, by rw [← hpar]; exact hty',
      by rw [← hpar]; exact hregs'⟩, by rw [hcs'.slotIds, hp.1.slots]⟩,
    rfl, rfl, rfl, ⟨b, hb, rfl, rfl⟩, rfl, rfl, Opt.GRX.of hR ?_, ?_⟩
  · have hfr : cs'.frame = ⟨g, cs'.frame.regs, cs'.frame.slots, b'.body, b'.term⟩ := by
      have h1 := hcs'.func
      cases hfr0 : cs'.frame with
      | mk fu re sl bo te =>
        rw [hfr0] at h1 hbody' hterm'
        simp only at h1 hbody' hterm'
        rw [h1, hbody', hterm']
    rw [hfr]
    exact hrel args cs'.frame.regs cs'.frame.slots (by rw [← hpar]; exact hty'.symm)
      (by rw [← hpar]; exact hregs') (by rw [hcs'.slotIds, hp.1.slots])
  · show Opt.CallersRelX _ _ [] cs'.callers
    rw [hcs'.callers]; exact .nil _

end OptRel

/-- `Opt.Reach` is `Clif.Reaches`. -/
theorem reaches_of {env : Clif.Env} {p : Clif.Program} {s u : Clif.State}
    (hr : Opt.Reach env p s u) : Clif.Reaches env p s u := by
  induction hr with
  | refl => exact .refl _
  | next h1 _ ih => exact .next h1 ih

theorem reach_of {env : Clif.Env} {p : Clif.Program} {s u : Clif.State}
    (hr : Clif.Reaches env p s u) : Opt.Reach env p s u := by
  induction hr with
  | refl => exact .refl _
  | next h1 _ ih => exact .next h1 ih

namespace OptRel

variable {P P' : Clif.Program} (h : OptRel P P')
include h

/-- **The optimised program's run refines the input program's run** from related entries; when
the input program's run returns or traps, the optimised run's call depth is bounded by the input
run's. -/
theorem refines {B : Clif.Env} (hE : Opt.EnvKeepsSymbols B) {cs cs' : Clif.State}
    {syms : String → Option Nat} (hS : Opt.SRX syms cs cs') (k : Nat) :
    ∃ n, (∀ v m, Clif.runLoop B P k cs = .returned v m → Clif.runLoop B P' n cs' = .returned v m) ∧
      (∀ c, Clif.runLoop B P k cs = .trapped c → Clif.runLoop B P' n cs' = .trapped c) ∧
      (Opt.Final (Clif.runLoop B P k cs) → ∀ d, Clif.DepthLe B P d cs →
        Clif.DepthLe B P' d cs') := by
  obtain ⟨n, ⟨h1, h2⟩, hd⟩ := Opt.runLoop_refinesX hE h.funsSim k cs cs' hS
  refine ⟨n, h1, h2, fun hf d hdl u hu => ?_⟩
  obtain ⟨v, hv, hl⟩ := hd hf u (reach_of hu)
  rw [← hl]
  exact hdl v (reaches_of hv)

end OptRel

end Link
