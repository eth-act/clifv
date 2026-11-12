import FV.E2E.LinkArmStage2Prog

/-!
# The invocation behind a related call (SEM1 #537, #680 (3), stage 2 glue)

Where `CallPost` of the CLIF invocation of count `n` is not vacuous at a call `(d, uses, w)` of
an activation of `g` (`RelatedN`, `Stage2Z`'s premise), one of its instances exists: the
invocation of count `n` returns, and is

* a call of a function `h` of `P` (`ProgInst`: the facts `stage2_answerF`'s oracle premise
  receives: the call's shape, the invocation, `h` a callee of `g`, the memory related to the
  world with the prophecies of call `n`, the arguments there, `h`'s returning run, and the body
  `sp`), or
* a call of a base extern `nm` (not a function of `P`), by name or through its address.

**`nv_cases`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **A program invocation behind a call** (module doc). -/
def ProgInst (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function) (F : BitVec 64 → Prop)
    (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (c : BitVec 64) (cs : Clif.State)
    (n : Nat) (d : Option String) (uses : List CV) (w : Arm.ArmState) (h : Clif.Function)
    (args : List CV) (vals : List Clif.Val) (cm : Clif.Mem) (cs' : Clif.State)
    (rvals : List Clif.Val) (cm' : Clif.Mem) : Prop :=
  (d = some h.name ∧ uses = args ∨
    d = none ∧ L.IndTo g h ∧ ∃ u, uses = u :: args ∧ lo64 u = L.Xb.sym h.name 0) ∧
  InvokedN (L.envOfB M g c) L.P.bare cs n h.name vals cm ∧ L.Callee g h ∧ 0 < M ∧
  MemRel F L.syms cm (L.worldPR κ M h (P n) (R n) w) ∧
  ArgsAt h.sig vals args (L.worldPR κ M h (P n) (R n) w) ∧
  StackArgsAvoid F h.sig vals (L.worldPR κ M h (P n) (R n) w) ∧
  SameWorld F w (L.worldPR κ M h (P n) (R n) w) ∧
  Clif.initState L.P h.name vals cm = .ok cs' ∧ L.crun M cs' = .returned rvals cm' ∧ spv w = c

/-- **The invocation behind a related call** (module doc). -/
theorem nv_cases (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop} {c : BitVec 64}
    (hdead : ∀ a, StackBelow (κ M g) c a → F a ∧ ¬ L.Img a)
    (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (cs : Clif.State) (n : Nat)
    {d : Option String} {uses : List CV} {w : Arm.ArmState}
    (hnv : ¬ ∀ r, CallPost ((L.envOfB M g c).only (InvokedN (L.envOfB M g c) L.P.bare cs n))
      (g.externs.map (·.2)) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
      L.Xb.sym d uses w r) :
    (∃ h ∈ L.P.funcs, ∃ args vals cm cs' rvals cm',
      L.ProgInst κ M g F P R c cs n d uses w h args vals cm cs' rvals cm') ∨
    (∃ nm vals cm, InvokedN (L.envOfB M g c) L.P.bare cs n nm vals cm ∧ L.P.func? nm = none ∧
      (d = some nm ∧ (∃ args, uses = args) ∨
        d = none ∧ ∃ u args, uses = u :: args ∧ lo64 u = L.Xb.sym nm 0)) := by
  -- the world with the prophecies of call `n` for the callee `h`, and its facts
  have hW : ∀ (h : Clif.Function) (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem),
      L.Callee g h → 0 < M →
      RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g c sl cm w →
      SameWorld F w (L.worldPR κ M h (P n) (R n) w) ∧
      RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g c sl cm (L.worldPR κ M h (P n) (R n) w) ∧
      spv (L.worldPR κ M h (P n) (R n) w) = spv w := by
    intro h sl cm hcal hM hmr
    have hsp : spv w = c := hmr.2.1
    have hsw : SameWorld F w (L.worldPR κ M h (P n) (R n) w) :=
      L.sameWorld_worldPR_of fun a ha => (hdead a (by
        rw [← hsp]; exact stackBelow_mono ha (L.budget_step hκ hM hg hcal))).1
    refine ⟨hsw, mrStable_relW _ g c sl cm _ _ ?_ hmr, ?_⟩
    · exact ⟨fun f hf _ => (hsw.1 f hf).symm, fun a ha => (hsw.2.1 a ha).symm, hsw.2.2.symm⟩
    · exact (hsw.1 (.GPR 31#5) (by simp [Masked])).symm
  refine Classical.byContradiction fun hno => hnv fun _ => ⟨?_, ?_⟩
  · -- an extern declaration of `g`
    intro ext hin G sl cm args vals rvals cm' hG hd hargs hmr hret hlen
    exfalso
    obtain ⟨hA, hb | ⟨h, hpf, hmay, -, cs', hinit, hrun⟩⟩ := L.envOfB_only_some hG hret
    · obtain ⟨hpf, -⟩ := hb
      refine hno (.inr ⟨ext.name, vals, cm, hA, hpf, ?_⟩)
      rcases hd with ⟨e, rfl⟩ | ⟨e, -, rfl⟩
      · exact .inl ⟨e, _, rfl⟩
      · exact .inr ⟨e, _, _, rfl, lo64_ofX _⟩
    · obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
      have hcal : L.Callee g h := .inr (.inl ⟨ext, hin, hpf⟩)
      have hM : 0 < M := by
        cases M with
        | zero => exact absurd hrun (hR.zero cs' rvals cm')
        | succ M => omega
      have hsig := hL.declSig g hg ext hin h hpf
      rw [hsig] at hargs
      obtain ⟨hsw, hmrW, hspW⟩ := hW h sl cm hcal hM hmr
      -- the stack-passed arguments are in the caller's outgoing area, outside `F`
      have hsav : StackArgsAvoid F h.sig vals w := by
        intro off v hm k hk
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
        rw [List.getElem?_zip_eq_some] at hi
        obtain ⟨hli, hvi⟩ := hi
        have hty := (clifEntry_initState (f := h) (by rw [hname]; exact hpf)
          (by rw [hname]; exact hinit)).sig
        obtain ⟨p, hp⟩ : ∃ p, h.sig.params[i]? = some p := by
          have := congrArg (·[i]?) hty
          simp only [List.getElem?_map, hvi, Option.map_some] at this
          cases hp : h.sig.params[i]? with
          | none => rw [hp] at this; cases this
          | some p => exact ⟨p, rfl⟩
        have hvp : v.ty = p.ty := by
          have := congrArg (·[i]?) hty
          simp only [List.getElem?_map, hvi, hp, Option.map_some, Option.some.injEq] at this
          exact this
        have hfit := hL.outFits g hg ext hin (by simp [hpf]) i off p (by rw [hsig]; exact hli)
          (by rw [hsig]; exact hp)
        rw [hvp] at hk
        rw [add_ofNat_add]
        have hav : Avoids F (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase (spv w) := hmr.1.2.2.2.1
        exact hav (off + k) (by omega)
      have hargsW : ArgsAt h.sig vals args (L.worldPR κ M h (P n) (R n) w) :=
        ⟨hargs.1, hargs.2.1, fun off v hm => by
          rw [show spOf (L.worldPR κ M h (P n) (R n) w) = spOf w from hspW]
          have e := hargs.2.2 off v hm
          rw [← e]
          congr 1
          exact read_mem_bytes_congr _ _ fun k hk => (hsw.2.1 _ (hsav off v hm k hk)).symm⟩
      have hsavW : StackArgsAvoid F h.sig vals (L.worldPR κ M h (P n) (R n) w) := by
        intro off v hm; rw [hspW]; exact hsav off v hm
      have hinv : InvokedN (L.envOfB M g c) L.P.bare cs n h.name vals cm := by
        rw [hname]; exact hA
      have hto : d = none → ext.colocated = false → L.IndTo g h := fun _ hcol => by
        refine ⟨by rw [hname]; exact hmay, ?_⟩
        rcases hmay with hdn | ⟨-, -, hall⟩
        · exact .inl ⟨by rw [hname]; exact hdn, ext, hin, hname.symm, hcol⟩
        · obtain ⟨sig, hs, hm⟩ := hall h hpf
          exact .inr ⟨sig, hs, hm, hm.returns_length⟩
      refine hno (.inl ⟨h, hh, args, vals, cm, cs', rvals, cm', ?_, hinv, hcal, hM, hmrW.1.1,
        hargsW, hsavW, hsw, by rw [hname]; exact hinit, hrun, hmr.2.1⟩)
      rcases hd with ⟨e, rfl⟩ | ⟨e, hcol, rfl⟩
      · exact .inl ⟨by rw [e, hname], rfl⟩
      · exact .inr ⟨e, hto e hcol, _, rfl, by rw [lo64_ofX, hname]⟩
  · -- an indirect call
    intro sig hsig nm G sl cm u args vals rvals cm' hdn hu hG hsg hlo hargsS hmr hret hrl hty
    exfalso
    obtain ⟨hA, hb | ⟨h, hpf, hdecl, -, cs', hinit, hrun⟩⟩ := L.envOfB_only_some hG hret
    · obtain ⟨hpf, -⟩ := hb
      exact hno (.inr ⟨nm, vals, cm, hA, hpf, .inr ⟨hdn, u, args, hu, hlo⟩⟩)
    · obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
      subst hname
      have hnf : ¬ Clif.IndFree g := fun hif => by
        rw [indSigs_nil_of_indFree hif] at hsig; cases hsig
      have hdeclS := hL.indSig g hg hnf
      have hcal : L.Callee g h := .inr (.inr ⟨hh, hdecl⟩)
      have hM : 0 < M := by
        cases M with
        | zero => exact absurd hrun (hR.zero cs' rvals cm')
        | succ M => omega
      have hce := clifEntry_initState (f := h) hpf hinit
      have hvl : vals.length = h.sig.params.length := by
        have := congrArg List.length hce.sig
        simpa using this
      have hm : IndSigMatch sig h :=
        hsg h.sig (by simp only [Clif.Env.only_sigOf, envOfB, Clif.linkEnvR_sigOf, hpf,
          Option.map_some])
      obtain ⟨⟨bytes, hb, hb8⟩, -⟩ := hdeclS h hh hdecl (.inl ⟨sig, hsig, hm⟩)
      have hall : AllHold vals args :=
        (argsAt_iff_of_regs (hm.paramBytes.trans hb) hb8 hargsS.1).mp hargsS
      obtain ⟨hsw, hmrW, -⟩ := hW h sl cm hcal hM hmr
      have hargsW : ArgsAt h.sig vals args (L.worldPR κ M h (P n) (R n) w) :=
        (argsAt_iff_of_regs hb hb8 hvl).mpr hall
      have hsavW : StackArgsAvoid F h.sig vals (L.worldPR κ M h (P n) (R n) w) := by
        intro off v hm
        obtain ⟨r, hr⟩ := (locsOf_small hb hb8).2 _ (List.of_mem_zip hm).1
        cases hr
      exact hno (.inl ⟨h, hh, args, vals, cm, cs', rvals, cm',
        .inr ⟨hdn, ⟨hdecl, .inr ⟨sig, hsig, hm, hm.returns_length⟩⟩, u, hu, hlo⟩, hA, hcal, hM,
        hmrW.1.1, hargsW, hsavW, hsw, hinit, hrun, hmr.2.1⟩)

end LinkSys

end E2E
