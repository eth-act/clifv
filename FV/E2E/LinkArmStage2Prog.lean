import FV.E2E.LinkArmProgResultBT

/-!
# Stage 2 at one call, from the program callee's oracle facts (SEM1 #537, #680 (3))

Stage 2 of call `n` (`Stage2Y`/`Stage2Z`) asks, where `CallPost` of the CLIF invocation of count
`n` is not vacuous, for an answer of `XPRBT … n` that `CallPost` accepts. As for stage 1 of the
non-slot statement (`xCallsOk`, `xCallsIndOk`), it suffices that every instance of `CallPost`
(an extern declaration, or an indirect call signature, that the call can stand for, whose
invocation returns) has an answer meeting its clause (`callPost_of_answers`): the answer is then
unique and accepted.

* At a base extern: `Xb`'s answer (`Ok.baseX`, `Ok.baseXI`).
* At a function `h` of `P`: `progXBT` from the world with the prophecies of call `n`
  (`worldPR … (P n) (R n) w`, `SameWorld` with `w` since the callee region is in `F`), by
  `progResultBT`, given the **oracle facts** of the invocation (`OracleAt`): the invocation's
  memory is placed at the body `sp` with some `ini` whose next slot bytes are the prophesied ones,
  and the canonical callee run's table is `calleeIni h ini`'s.

* `callPost_of_answers`, `envOfB_only_some`, `sameWorld_worldPR_of`;
* `OracleAt`; **`stage2_answer`**: stage 2 at one call `(d, uses, w)` from `OracleAt` at its
  program instances.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **Answers at every instance give an accepted answer**: if at every instance of `CallPost`
of the call `(d, uses, w)` the semantics `X` answers a result meeting the instance's clause, then
where `CallPost` is not vacuous `X`'s answer exists and is accepted. -/
theorem callPost_of_answers {env : Clif.Env} {exts : List Clif.ExtFunc}
    {sigs : List Clif.Signature} {MR : MemRelT} {sym : String → Int → BitVec 64} {X : ExtSem}
    {d : Option String} {uses : List CV} {w : Arm.ArmState}
    (hext : ∀ ext ∈ exts, ∀ G (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem) (args : List CV)
      (vals rvals : List Clif.Val) (cm' : Clif.Mem),
      env.extern ext.name = some G →
      (d = some ext.name ∧ uses = args ∨
        d = none ∧ ext.colocated = false ∧ uses = ofX (sym ext.name 0) :: args) →
      ArgsAt ext.sig vals args w → MR sl cm w →
      G vals cm = .returned rvals cm' → rvals.length = ext.sig.returns.length →
      ∃ r, X.call d uses w = some r ∧
        r.1.length = ext.sig.returns.length ∧ PrefixHold rvals r.1 ∧ MR sl cm' r.2)
    (hind : ∀ sig ∈ sigs, ∀ (n : String) G (sl : List (Clif.SlotId × Nat)) (cm : Clif.Mem) (u : CV)
      (args : List CV) (vals rvals : List Clif.Val) (cm' : Clif.Mem),
      d = none → uses = u :: args →
      env.extern n = some G → (∀ s, env.sigOf n = some s → sig.abiMatch s = true) →
      lo64 u = sym n 0 →
      vals.length ≤ 8 → AllHold vals args → MR sl cm w →
      G vals cm = .returned rvals cm' → rvals.length = sig.returns.length →
      vals.map (·.ty) = Clif.AbiParam.tys sig.params →
      ∃ r, X.call d uses w = some r ∧
        r.1.length = sig.returns.length ∧ PrefixHold rvals r.1 ∧ MR sl cm' r.2)
    (hnv : ¬ ∀ r, CallPost env exts sigs MR sym d uses w r) :
    ∃ x, X.call d uses w = some x ∧ CallPost env exts sigs MR sym d uses w x := by
  cases hx : X.call d uses w with
  | none =>
    exfalso
    refine hnv fun _ => ⟨fun ext hin G sl cm args vals rvals cm' hG hd ha hmr hr hl => ?_,
      fun sig hs n G sl cm u args vals rvals cm' hdn hu hG hsg hlo h8 hall hmr hr hl hty => ?_⟩
    · obtain ⟨r', hr', -⟩ := hext ext hin G sl cm args vals rvals cm' hG hd ha hmr hr hl
      rw [hx] at hr'; cases hr'
    · obtain ⟨r', hr', -⟩ := hind sig hs n G sl cm u args vals rvals cm' hdn hu hG hsg hlo h8 hall
        hmr hr hl hty
      rw [hx] at hr'; cases hr'
  | some x =>
    refine ⟨x, rfl, fun ext hin G sl cm args vals rvals cm' hG hd ha hmr hr hl => ?_,
      fun sig hs n G sl cm u args vals rvals cm' hdn hu hG hsg hlo h8 hall hmr hr hl hty => ?_⟩
    · obtain ⟨r', hr', h1, h2, h3⟩ := hext ext hin G sl cm args vals rvals cm' hG hd ha hmr hr hl
      rw [hx] at hr'; cases hr'
      exact ⟨h1, h2, h3⟩
    · obtain ⟨r', hr', h1, h2, h3⟩ := hind sig hs n G sl cm u args vals rvals cm' hdn hu hG hsg
        hlo h8 hall hmr hr hl hty
      rw [hx] at hr'; cases hr'
      exact ⟨h1, h2, h3⟩

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **A returning extern of `envOfB` restricted to `A`**: the invocation is admitted, and the
extern is the base's, or a function `h` of `P` that `g` may call whose run (`crun M`) from a
placed memory returns. -/
theorem envOfB_only_some {M : Nat} {g : Clif.Function} {c : BitVec 64}
    {A : String → List Clif.Val → Clif.Mem → Prop} {n : String}
    {G : List Clif.Val → Clif.Mem → Clif.Outcome}
    (hG : ((L.envOfB M g c).only A).extern n = some G) {vals : List Clif.Val} {cm : Clif.Mem}
    {rvals : List Clif.Val} {cm' : Clif.Mem} (hr : G vals cm = .returned rvals cm') :
    A n vals cm ∧
      ((L.P.func? n = none ∧ ∃ G0, L.base.extern n = some G0 ∧ G0 vals cm = .returned rvals cm') ∨
       ∃ h, L.P.func? n = some h ∧ L.MayCall g n ∧ (L.NeedSlots → L.PlacedB cm c) ∧
        ∃ cs, Clif.initState L.P n vals cm = .ok cs ∧ L.crun M cs = .returned rvals cm') := by
  obtain ⟨G1, hG1, rfl⟩ := Clif.Env.only_extern_eq hG
  obtain ⟨hA, hr'⟩ := onlyFn_returned hr
  refine ⟨hA, ?_⟩
  cases hpf : L.P.func? n with
  | none =>
    simp only [envOfB, hpf, Option.isSome_none, Bool.false_eq_true, false_and, ↓reduceIte,
      Clif.linkEnvR_none hpf] at hG1
    exact .inl ⟨rfl, G1, hG1, hr'⟩
  | some h =>
    refine .inr ⟨h, rfl, ?_⟩
    simp only [envOfB, hpf, Option.isSome_some, true_and, Clif.linkEnvR_some hpf,
      Option.map_some] at hG1
    split at hG1
    · cases hG1
    · rename_i hmay
      refine ⟨Classical.byContradiction fun hn => hmay ⟨by simp [hpf], hn⟩, ?_⟩
      simp only [↓reduceIte, Option.some.injEq] at hG1
      subst hG1
      simp only at hr'
      split at hr'
      · rename_i hpl
        refine ⟨hpl, ?_⟩
        revert hr'
        cases hi : Clif.initState L.P n vals cm with
        | ok cs => intro hr'; exact ⟨cs, rfl, hr'⟩
        | trap c' => intro hr'; cases hr'
        | stuck m' => intro hr'; cases hr'
      · cases hr'

/-- **The world with the prophecies of a call is the same world** when the callee region is in
`F`. -/
theorem sameWorld_worldPR_of {M : Nat} {h : Clif.Function} {F : BitVec 64 → Prop}
    {Pn : BitVec 64 → BitVec 8} {Sn w : Arm.ArmState}
    (hdead : ∀ a, L.calleeRgn κ M h w a → F a) :
    SameWorld F w (L.worldPR κ M h Pn Sn w) :=
  ⟨fun f hf => (L.r_worldPR_out h _ _ w (fun hm => hf hm.1)).symm,
    fun a ha => by
      rw [L.mem_worldPR, worldP, mem_overlay_out (R := L.calleeRgn κ M h w)
        (fun hr => ha (hdead a hr))],
    (L.program_worldPR h _ _ w).symm⟩

/-- **The oracle facts of a program invocation**: its memory `cm` is placed at the body `sp` `c`
with some `ini` whose next slot bytes are those of the world `W` (under `NeedSlots`), and the
canonical callee run from `W` with the arguments `args` has the table of `calleeIni h ini`. -/
def OracleAt (κ : Nat → Clif.Function → Nat) (M : Nat) (h : Clif.Function) (c : BitVec 64)
    (cm : Clif.Mem) (args : List CV) (W : Arm.ArmState) : Prop :=
  ∃ ini : Clif.SlotInit, (L.NeedSlots → L.PlaceAtB cm c ini) ∧
    (L.NeedSlots → ∀ a, L.SlotByte h c a → ini.bytes (ini.next + 1) a = W.mem (BitVec.ofNat 64 a)) ∧
    L.TableOf (M - 1) h (enterAt (L.A h) (L.canon h args W)) (calleeIni h ini)

/-- **Stage 2 at one call, with the invocation's facts** (`stage2_answer` whose oracle premise
`hor` also receives the facts stage 2 derives at the invocation: the callee memory related to the
world with the prophecies, the arguments there, and the callee's returning run). -/
theorem stage2_answerFRU (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRBRU κ (M - 1))
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ M g ≤ c.toNat) (hdead : ∀ a, StackBelow (κ M g) c a → F a ∧ ¬ L.Img a)
    (halign : c.toNat % 16 = 0)
    (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (cs : Clif.State) (n : Nat)
    {d : Option String} {uses : List CV} {w : Arm.ArmState}
    (hor : ∀ h ∈ L.P.funcs, ∀ (args : List CV) (vals : List Clif.Val) (cm : Clif.Mem)
      (cs' : Clif.State) (rvals : List Clif.Val) (cm' : Clif.Mem),
      (d = some h.name ∧ uses = args ∨
        d = none ∧ L.IndTo g h ∧ ∃ u, uses = u :: args ∧ lo64 u = L.Xb.sym h.name 0) →
      InvokedN (L.envOfB M g c) L.P.bare cs n h.name vals cm →
      L.Callee g h → 0 < M →
      MemRel F L.syms cm (L.worldPR κ M h (P n) (R n) w) →
      ArgsAt h.sig vals args (L.worldPR κ M h (P n) (R n) w) →
      StackArgsAvoid F h.sig vals (L.worldPR κ M h (P n) (R n) w) →
      SameWorld F w (L.worldPR κ M h (P n) (R n) w) → spv w = c →
      Clif.initState L.P h.name vals cm = .ok cs' → L.crun M cs' = .returned rvals cm' →
      L.OracleAt κ M h c cm args (L.worldPR κ M h (P n) (R n) w))
    (hnv : ¬ ∀ r, CallPost ((L.envOfB M g c).only (InvokedN (L.envOfB M g c) L.P.bare cs n))
      (g.externs.map (·.2)) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
      L.Xb.sym d uses w r) :
    ∃ x, (L.XPRBT κ M g F P R n).call d uses w = some x ∧
      CallPost ((L.envOfB M g c).only (InvokedN (L.envOfB M g c) L.P.bare cs n))
        (g.externs.map (·.2)) (indSigs g)
        (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
        L.Xb.sym d uses w x := by
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
  refine callPost_of_answers ?_ ?_ hnv
  · -- an extern declaration of `g`
    intro ext hin G sl cm args vals rvals cm' hG hd hargs hmr hret hlen
    obtain ⟨hA, hb | ⟨h, hpf, hmay, -, cs', hinit, hrun⟩⟩ := L.envOfB_only_some hG hret
    · obtain ⟨hpf, G0, hG0, hr0⟩ := hb
      obtain ⟨outs, w', hx, h1, h2, h3⟩ := hL.baseX g hg F (L.A g).af.slotBase
        (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase c ext
        (List.mem_filter.mpr ⟨hin, by simp [hpf]⟩) G0 sl cm w d uses args vals rvals cm' hG0 hd
        hargs hmr hr0 hlen
      refine ⟨(outs, w'), ?_, h1, h2, h3⟩
      rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, -, rfl⟩
      · rw [L.XPRBT_base hpf]; exact hx
      · rw [L.XPRBT_none (by
          show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 (ofX (L.Xb.sym ext.name 0))) = none
          rw [lo64_ofX]; exact (L.find_sym hL ext.name).2 hpf)]
        exact hx
    · obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
      have hcal : L.Callee g h := .inr (.inl ⟨ext, hin, hpf⟩)
      have hM : 0 < M := by
        cases M with
        | zero => exact absurd hrun (hR.zero cs' rvals cm')
        | succ M => omega
      have hsig := hL.declSig g hg ext hin h hpf
      rw [hsig] at hargs
      obtain ⟨hsw, hmrW, hspW⟩ := hW h sl cm hcal hM hmr
      have hsp : spv w = c := hmr.2.1
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
      -- the arguments at the world with the prophecies
      have hargsW : ArgsAt h.sig vals args (L.worldPR κ M h (P n) (R n) w) :=
        ⟨hargs.1, hargs.2.1, fun off v hm => by
          rw [show spOf (L.worldPR κ M h (P n) (R n) w) = spOf w from hspW]
          have e := hargs.2.2 off v hm
          rw [← e]
          congr 1
          exact read_mem_bytes_congr _ _ fun k hk => (hsw.2.1 _ (hsav off v hm k hk)).symm⟩
      have hsavW : StackArgsAvoid F h.sig vals (L.worldPR κ M h (P n) (R n) w) := by
        intro off v hm; rw [hspW]; exact hsav off v hm
      -- the oracle facts
      have hinv : InvokedN (L.envOfB M g c) L.P.bare cs n h.name vals cm := by
        rw [hname]; exact hA
      have hto : d = none → ext.colocated = false → L.IndTo g h := fun _ hcol => by
        refine ⟨by rw [hname]; exact hmay, ?_⟩
        rcases hmay with hdn | ⟨-, -, hall⟩
        · exact .inl ⟨by rw [hname]; exact hdn, ext, hin, hname.symm, hcol⟩
        · obtain ⟨sig, hs, hm⟩ := hall h hpf
          exact .inr ⟨sig, hs, hm, hm.returns_length⟩
      obtain ⟨ini, hpl, hslotb, htab⟩ := hor h hh args vals cm _ rvals cm'
        (by rcases hd with ⟨e, rfl⟩ | ⟨e, hcol, rfl⟩
            · exact .inl ⟨by rw [e, hname], rfl⟩
            · exact .inr ⟨e, hto e hcol, _, rfl, by rw [lo64_ofX, hname]⟩) hinv hcal hM hmrW.1.1
        hargsW hsavW hsw hsp (by rw [hname]; exact hinit) hrun
      obtain ⟨outs, w', hx, hol, hho, hmr'⟩ :=
        L.progResultBTRU hL hκ ih hdet hg hh hcal himgF hroom hdead halign hargsW hsavW hmrW hpl
          hslotb htab (by rw [hname]; exact hinit) hrun
      refine ⟨(outs, w'), ?_, by rw [hol, hsig], hho, hmr'⟩
      rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, hcol, rfl⟩
      · rw [L.XPRBT_prog hpf]; exact hx
      · have hs : symCallee L.Xb L.P (lo64 (ofX (L.Xb.sym ext.name 0))) = some h := by
          show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 (ofX (L.Xb.sym ext.name 0))) = some h
          rw [lo64_ofX]; exact (L.find_sym hL ext.name).1 h hpf
        have hto := hto rfl hcol
        rw [L.XPRBT_ind hs, if_pos ⟨hto, argsAt_regLocs hargsW⟩]
        exact hx
  · -- an indirect call
    intro sig hsig nm G sl cm u args vals rvals cm' hdn hu hG hsg hlo hl8 hall hmr hret hrl hty
    obtain ⟨hA, hb | ⟨h, hpf, hdecl, -, cs', hinit, hrun⟩⟩ := L.envOfB_only_some hG hret
    · obtain ⟨hpf, G0, hG0, hr0⟩ := hb
      have hs : symCallee L.Xb L.P (lo64 u) = none := by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = none
        rw [hlo]; exact (L.find_sym hL nm).2 hpf
      subst hdn hu
      obtain ⟨outs, w', hx, h1, h2, h3⟩ := hL.baseXI g hg F (L.A g).af.slotBase
        (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase c sig hsig nm G0 sl cm w u args vals rvals
        cm' hG0 (fun _ h => nomatch h) hlo hl8 hall hmr hr0 hrl hty
      exact ⟨(outs, w'), by rw [L.XPRBT_none hs]; exact hx, h1, h2, h3⟩
    · obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
      subst hname
      have hnf : ¬ Clif.IndFree g := fun hif => by
        rw [indSigs_nil_of_indFree hif] at hsig; cases hsig
      have hdeclS := hL.indSig g hg hnf
      have hs : symCallee L.Xb L.P (lo64 u) = some h := by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = some h
        rw [hlo]; exact (L.find_sym hL h.name).1 h hpf
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
      obtain ⟨⟨bytes, hb, hb8⟩, hsr⟩ := hdeclS h hh hdecl (.inl ⟨sig, hsig, hm⟩)
      obtain ⟨hsw, hmrW, hspW⟩ := hW h sl cm hcal hM hmr
      have hargsW : ArgsAt h.sig vals args (L.worldPR κ M h (P n) (R n) w) :=
        (argsAt_iff_of_regs hb hb8 hvl).mpr hall
      have hsavW : StackArgsAvoid F h.sig vals (L.worldPR κ M h (P n) (R n) w) := by
        intro off v hm
        obtain ⟨r, hr⟩ := (locsOf_small hb hb8).2 _ (List.of_mem_zip hm).1
        cases hr
      obtain ⟨ini, hpl, hslotb, htab⟩ := hor h hh args vals cm _ rvals cm'
        (.inr ⟨hdn, ⟨hdecl, .inr ⟨sig, hsig, hm, hm.returns_length⟩⟩, u, hu, hlo⟩) hA
        hcal hM hmrW.1.1 hargsW hsavW hsw hmr.2.1 hinit hrun
      obtain ⟨outs, w', hx, hol, hho, hmr'⟩ :=
        L.progResultBTRU hL hκ ih hdet hg hh hcal himgF hroom hdead halign hargsW hsavW hmrW hpl
          hslotb htab hinit hrun
      subst hdn hu
      refine ⟨(outs, w'), ?_, ?_, hho, hmr'⟩
      · rw [L.XPRBT_ind hs, if_pos ⟨⟨hdecl, .inr ⟨sig, hsig, hm, hm.returns_length⟩⟩,
          argsAt_regLocs hargsW⟩]
        exact hx
      · rw [hol]
        exact hm.returns_length

/-- **Stage 2 at one call, with the invocation's facts, determinism `DetPRBR`**
(`stage2_answerFRU` with `DetPRBR.toU`). -/
theorem stage2_answerFR (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRBR κ (M - 1))
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ M g ≤ c.toNat) (hdead : ∀ a, StackBelow (κ M g) c a → F a ∧ ¬ L.Img a)
    (halign : c.toNat % 16 = 0)
    (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (cs : Clif.State) (n : Nat)
    {d : Option String} {uses : List CV} {w : Arm.ArmState}
    (hor : ∀ h ∈ L.P.funcs, ∀ (args : List CV) (vals : List Clif.Val) (cm : Clif.Mem)
      (cs' : Clif.State) (rvals : List Clif.Val) (cm' : Clif.Mem),
      (d = some h.name ∧ uses = args ∨
        d = none ∧ L.IndTo g h ∧ ∃ u, uses = u :: args ∧ lo64 u = L.Xb.sym h.name 0) →
      InvokedN (L.envOfB M g c) L.P.bare cs n h.name vals cm →
      L.Callee g h → 0 < M →
      MemRel F L.syms cm (L.worldPR κ M h (P n) (R n) w) →
      ArgsAt h.sig vals args (L.worldPR κ M h (P n) (R n) w) →
      StackArgsAvoid F h.sig vals (L.worldPR κ M h (P n) (R n) w) →
      SameWorld F w (L.worldPR κ M h (P n) (R n) w) → spv w = c →
      Clif.initState L.P h.name vals cm = .ok cs' → L.crun M cs' = .returned rvals cm' →
      L.OracleAt κ M h c cm args (L.worldPR κ M h (P n) (R n) w))
    (hnv : ¬ ∀ r, CallPost ((L.envOfB M g c).only (InvokedN (L.envOfB M g c) L.P.bare cs n))
      (g.externs.map (·.2)) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
      L.Xb.sym d uses w r) :
    ∃ x, (L.XPRBT κ M g F P R n).call d uses w = some x ∧
      CallPost ((L.envOfB M g c).only (InvokedN (L.envOfB M g c) L.P.bare cs n))
        (g.externs.map (·.2)) (indSigs g)
        (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
        L.Xb.sym d uses w x :=
  L.stage2_answerFRU hL hκ ih (fun h => DetPRBR.toU L (hdet h)) hg himgF hroom hdead halign P R cs
    n hor hnv

/-- **Stage 2 at one call, with the invocation's facts** (`stage2_answerFR` with `DetPRB`). -/
theorem stage2_answerF (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRB κ (M - 1))
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ M g ≤ c.toNat) (hdead : ∀ a, StackBelow (κ M g) c a → F a ∧ ¬ L.Img a)
    (halign : c.toNat % 16 = 0)
    (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (cs : Clif.State) (n : Nat)
    {d : Option String} {uses : List CV} {w : Arm.ArmState}
    (hor : ∀ h ∈ L.P.funcs, ∀ (args : List CV) (vals : List Clif.Val) (cm : Clif.Mem)
      (cs' : Clif.State) (rvals : List Clif.Val) (cm' : Clif.Mem),
      (d = some h.name ∧ uses = args ∨
        d = none ∧ L.IndTo g h ∧ ∃ u, uses = u :: args ∧ lo64 u = L.Xb.sym h.name 0) →
      InvokedN (L.envOfB M g c) L.P.bare cs n h.name vals cm →
      L.Callee g h → 0 < M →
      MemRel F L.syms cm (L.worldPR κ M h (P n) (R n) w) →
      ArgsAt h.sig vals args (L.worldPR κ M h (P n) (R n) w) →
      StackArgsAvoid F h.sig vals (L.worldPR κ M h (P n) (R n) w) →
      SameWorld F w (L.worldPR κ M h (P n) (R n) w) → spv w = c →
      Clif.initState L.P h.name vals cm = .ok cs' → L.crun M cs' = .returned rvals cm' →
      L.OracleAt κ M h c cm args (L.worldPR κ M h (P n) (R n) w))
    (hnv : ¬ ∀ r, CallPost ((L.envOfB M g c).only (InvokedN (L.envOfB M g c) L.P.bare cs n))
      (g.externs.map (·.2)) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
      L.Xb.sym d uses w r) :
    ∃ x, (L.XPRBT κ M g F P R n).call d uses w = some x ∧
      CallPost ((L.envOfB M g c).only (InvokedN (L.envOfB M g c) L.P.bare cs n))
        (g.externs.map (·.2)) (indSigs g)
        (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
        L.Xb.sym d uses w x :=
  L.stage2_answerFR hL hκ ih (fun h => DetPRB.toR L (hdet h)) hg himgF hroom hdead halign P R cs n
    hor hnv

/-- **Stage 2 at one call** `(d, uses, w)` of an activation of `g` (body `sp` `c`, `g`'s stack
facts) at count `n`: where `CallPost` of the invocation of count `n` is not vacuous, `XPRBT … n`
answers an accepted result, given the oracle facts (`OracleAt`) of the program invocations of
count `n` for the arguments the call passes (`stage2_answerF`). -/
theorem stage2_answer (hL : L.Ok) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRB κ (M - 1))
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ M g ≤ c.toNat) (hdead : ∀ a, StackBelow (κ M g) c a → F a ∧ ¬ L.Img a)
    (halign : c.toNat % 16 = 0)
    (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (cs : Clif.State) (n : Nat)
    {d : Option String} {uses : List CV} {w : Arm.ArmState}
    (hor : ∀ h ∈ L.P.funcs, ∀ (args : List CV) (vals : List Clif.Val) (cm : Clif.Mem),
      (d = some h.name ∧ uses = args ∨ d = none ∧ ∃ u, uses = u :: args) →
      InvokedN (L.envOfB M g c) L.P.bare cs n h.name vals cm →
      L.OracleAt κ M h c cm args (L.worldPR κ M h (P n) (R n) w))
    (hnv : ¬ ∀ r, CallPost ((L.envOfB M g c).only (InvokedN (L.envOfB M g c) L.P.bare cs n))
      (g.externs.map (·.2)) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
      L.Xb.sym d uses w r) :
    ∃ x, (L.XPRBT κ M g F P R n).call d uses w = some x ∧
      CallPost ((L.envOfB M g c).only (InvokedN (L.envOfB M g c) L.P.bare cs n))
        (g.externs.map (·.2)) (indSigs g)
        (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
        L.Xb.sym d uses w x :=
  L.stage2_answerF hL hκ ih hdet hg himgF hroom hdead halign P R cs n
    (fun h hh args vals cm _ _ _ hd hA _ _ _ _ _ _ _ _ _ => hor h hh args vals cm
      (hd.imp id fun ⟨e, _, u, hu, _⟩ => ⟨e, u, hu⟩) hA) hnv

end LinkSys

end E2E
