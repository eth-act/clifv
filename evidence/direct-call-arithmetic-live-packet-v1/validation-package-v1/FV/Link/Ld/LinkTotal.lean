import FV.Link.Ld.PlanProof
import FV.Link.Ld.RelsTotal

/-! # `lean-ld` links its inputs (A1e, #409)

`link` (`FV/Link/Ld/Layout.lean`) resolves the inputs, collects the garbage, lays out, assembles
the plan and checks that the image's headers and tables fit their fields (`hdrFitsB`,
`tabsFitB`). From conditions decided before any relocation is applied or any byte is written:

* the layout's references resolve (`layRefsB`, address-free, `FV/Link/Ld/LayoutTotal.lean`):
  `layout` returns a plan;
* the relocations apply (`relsInB`, address-free, `FV/Link/Ld/RelsTotal.lean`): `assemble`
  builds its image;
* the headers and tables fit (`fitsB`): decided on the placement's image skeleton
  (`Lay.skel`: the entry, the program headers, the output sections and symbols of the plan, a
  body of the plan's size; the writer's fit checks read the body's size only, `hdrFitsB_body`,
  `tabsFitB_body`).

**`link_okIn`**: then `link o ins` succeeds, with `layout`'s plan.
-/

namespace Link.Ld

/-- **The image skeleton of a placement**: the entry `e`, the plan's program headers, output
sections and symbols, and a zero body of the plan's size (no piece: no relocation applied). -/
def Lay.skel (L : Lay) (o : Opts) (st : St) (g : GcOut) (e : Nat) : Img :=
  let pl := L.plan o e [] (L.syms o st g).1
  { entry := e, phs := pl.phdrs, body := ⟨Array.replicate pl.size 0⟩, secs := pl.secs, syms := pl.syms }

/-- **The headers and tables of `lean-ld`'s output fit their fields** (`hdrFitsB`, `tabsFitB`),
decided on the placement's image skeleton (`Lay.skel`). -/
def fitsB (o : Opts) (st : St) (g : GcOut) : Bool :=
  match (layPre o st g).entry o st g with
  | .ok e => ((layPre o st g).skel o st g e).hdrFitsB && ((layPre o st g).skel o st g e).tabsFitB
  | .error _ => false

/-- The fit checks read the body's size only. -/
theorem tabs_body (img : Img) (b : ByteArray) (h : b.size = img.body.size) :
    ({ img with body := b } : Img).tabs = img.tabs := by
  simp only [Img.tabs, Img.secNames, pad8_size, h]

theorem hdrFitsB_body (img : Img) (b : ByteArray) (h : b.size = img.body.size) :
    ({ img with body := b } : Img).hdrFitsB = img.hdrFitsB := by
  have ht := tabs_body img b h
  unfold Img.hdrFitsB
  rw [ht, h]

theorem tabsFitB_body (img : Img) (b : ByteArray) (h : b.size = img.body.size) :
    ({ img with body := b } : Img).tabsFitB = img.tabsFitB := by
  have ht := tabs_body img b h
  unfold Img.tabsFitB
  rw [ht]
  rfl

/-- **A plan `layout` returns** is the placement's plan of its entry, pieces and symbols. -/
theorem layout_parts {o : Opts} {st : St} {g : GcOut} {pl : Plan} {m : String}
    (h : layout o st g = .ok (pl, m)) :
    ∃ e ps, (layPre o st g).entry o st g = .ok e ∧ (layPre o st g).pieces o st g = .ok ps ∧
      pl = (layPre o st g).plan o e ps ((layPre o st g).syms o st g).1 := by
  unfold layout at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i ps hps
  split at h
  · cases h
  rename_i e he
  rcases hsy : (layPre o st g).syms o st g with ⟨syms, ms⟩
  simp only [hsy, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨e, ps, he, hps, h.1.symm⟩

/-- **`lean-ld` links its inputs**: when resolution and the garbage collection succeed, the
layout's references resolve (`layRefsB`), its relocations apply (`relsInB`) and the headers
and tables fit (`fitsB`), `link` succeeds with `layout`'s plan. -/
theorem link_okIn {o : Opts} {ins : List Input} {st : St} {g : GcOut}
    (hres : resolve (o.entry :: o.undefs) ins = .ok st) (hgc : st.gc (o.entry :: o.undefs) o.gc = .ok g)
    (hrefs : layRefsB o st g = true) (hrels : relsInB o st g = true) (hfit : fitsB o st g = true) :
    ∃ r, link o ins = .ok r ∧ layout o st g = .ok (r.plan, r.map) := by
  obtain ⟨pl, m, hl⟩ := layout_ok hrefs
  obtain ⟨body, hb⟩ := buildBody_layout hl (layout_relsOk hl hrels)
  have ha := assemble_layout hl hb
  have hbs := buildBody_size hb
  obtain ⟨e, ps, he, -, hpl⟩ := layout_parts hl
  unfold fitsB at hfit
  rw [he] at hfit
  simp only [Bool.and_eq_true] at hfit
  have himg : ({ entry := pl.entry, phs := pl.phdrs, body, secs := pl.secs, syms := pl.syms } : Img) =
      { (layPre o st g).skel o st g e with body := body } := by
    subst hpl; rfl
  have hsz : body.size = ((layPre o st g).skel o st g e).body.size := by
    rw [hbs, hpl]
    show _ = (⟨Array.replicate _ 0⟩ : ByteArray).size
    simp only [ByteArray.size, Array.size_replicate]
    rfl
  have h1 := hdrFitsB_body _ _ hsz
  have h2 := tabsFitB_body _ _ hsz
  rw [← himg, hfit.1] at h1
  rw [← himg, hfit.2] at h2
  refine ⟨⟨{ entry := pl.entry, phs := pl.phdrs, body, secs := pl.secs, syms := pl.syms }, m, pl⟩, ?_, hl⟩
  unfold link
  simp only [bind, Except.bind, hres, hgc, hl, ha, h1, h2, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, pure, Except.pure]

end Link.Ld
