import FV.Concurrency.CallSeg
import FV.Concurrency.LinkedMachine
import FV.Concurrency.ArmAllocEntry
import FV.E2E.EmitEnc
import FV.E2E.Binary

/-!
# The callee's entry on the linked machine, at the Arm level (#473, step (3))

From the caller's register-level relation `Q` at a direct `call` item of a linked function, the
linked machine `Link.M` steps the caller's `bl` into the callee and the callee's activation starts
related:

* `LFn.Static`: the static facts of `RL.Wf` for a compiled function (pipeline, layout, the entry
  `args` reading argument registers only); `Link.act_wf`: an activation of such a function with
  room for its frame and callees, entered on its program, its kept addresses outside its stack, is
  `Wf`;
* **`Link.step_call`**: at a `call` item to `n` the machine's step is the `bl`, which enters `n`'s
  code (`Link.enter`), without events, plain;
* **`Link.enter_call`**: the callee's activation `L.act FB (Link.enter FB x) KB GB` is `Wf`, its
  ABI entry is an `AbiCall` returning after the `bl`, it agrees with the caller's state but in the
  pc and `x30` and has its memory (the premises of `resume_premises_of_retC`), and after its
  prologue `Q`/`AInv` hold at its initial configuration (`q_init_lines`): the start of
  `arm_isel_refines_entryCRN`.
-/

namespace Concurrency.LinkedMachine

open Arm ArmFoot ArmThread ArmInstFoot Backend Backend.Proof ArmAllocThread E2E

/-- **The static facts of `RL.Wf` for a compiled function** (module doc). -/
structure LFn.Static (F : LFn) : Prop where
  check : AllocChecked F.vc F.rf
  alloc : lowerRFunc F.vc F.rf = .ok F.af
  emit : emitFunc F.fa.k F.af = .ok F.fa
  layout : F.fa.layout = .ok F.fb
  lm : labelOffsets F.fa.lines = .ok F.lm
  fit : 4 * F.fb.words.size ≤ 2 ^ 64
  psF : ∃ body, blocksLinesE ⟨F.fa.k, F.af.slotBase⟩ F.af F.af.blocks.toList {} = .ok (body, F.psF)
  entryArg : ∀ r, F.vc.EntryArg r → r.isArgReg = true

/-- **The state after the prologue does not depend on the activation's hooks**: the prologue's
lines are not hooked, and from the ABI entry both machines run them as `execLines`
(`prologue_linesAt`). -/
theorem _root_.Backend.Proof.RL.sP_hooks {R : RL} (hR : R.Wf) {ra : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0) (H : ArmHooks) : ({ R with H := H } : RL).sP = R.sP := by
  have hR' : ({ R with H := H } : RL).Wf :=
    ⟨hR.check, hR.alloc, hR.emit, hR.layout, hR.lm, hR.fit, hR.stack, hR.psF, hR.prog0, hR.gfree⟩
  have h1 := (prologue_linesAt hR hent).run
  have h2 := (prologue_linesAt hR' hent).run
  exact Option.some.inj (h2.symm.trans h1)

/-- `StRel` does not depend on the activation's hooks, given that the state after the prologue
does not (`RL.sP_hooks`; `StRel.fplr` compares with the prologue's image `R.topImg`, read after
the prologue run by `R.step`, which mentions the hooks). -/
theorem _root_.Backend.Proof.StRel.hooks {R : RL} (H : ArmHooks)
    (hP : ({ R with H := H } : RL).sP = R.sP) {s : ArmState} {m : Loc → CV}
    {w : ArmState} (h : StRel R s m w) : StRel { R with H := H } s m w :=
  ⟨h.store, h.world, h.err, h.prog, h.sp, h.align, fun hf => by
    show Arm.read_mem_bytes R.topN R.topB s =
      Arm.read_mem_bytes R.topN R.topB ({ R with H := H } : RL).sP
    rw [hP]; exact h.fplr hf, h.code, h.gkeep, h.fp⟩

/-- **`Q` does not depend on the activation's hooks** (e.g. a function's activation on the linked
machine and on a per-function machine), given that the state after the prologue does not
(`RL.sP_hooks`; see `StRel.hooks`). -/
theorem _root_.Backend.Proof.Q.hooks {R : RL} (H : ArmHooks)
    (hP : ({ R with H := H } : RL).sP = R.sP) {s : ArmState}
    {c : MConf CV ArmState} (h : Q R s c) : Q { R with H := H } s c := by
  match c, h with
  | .run ⟨b, its, m, w⟩, ⟨j, vb, items, pre, code, ls, ps1, ps2, T, h1, h2, h3, h4, h5, h6, h7, h8,
      h9, hst⟩ => exact ⟨j, vb, items, pre, code, ls, ps1, ps2, T, h1, h2, h3, h4, h5, h6, h7, h8,
      h9, hst.hooks H hP⟩
  | .ret .., _ => trivial
  | .halt _, _ => trivial

namespace Link

variable {L : Link}

/-- **An activation of a statically checked function is `Wf`** (module doc). -/
theorem act_wf {F : LFn} (hF : F.Static) {s0 : ArmState} {K : Nat} {G : BitVec 64 → Prop}
    (hst : StackAvail K F.af s0) (hp : s0.program = F.fb.program F.base)
    (hg : ∀ a, G a → ¬ StackBelow (frameDrop F.af + K) (spv s0) a) : (L.act F s0 K G).Wf :=
  ⟨hF.check, hF.alloc, hF.emit, hF.layout, hF.lm, hF.fit, hst, hF.psF, hp, hg⟩

/-- **The step at a direct `call` item is the `bl` into the callee** (module doc). -/
theorem step_call (hL : L.Ok) {nA nB : String} {FA FB : LFn} (hA : (nA, FA) ∈ L.fns)
    (hB : (nB, FB) ∈ L.fns) {s0 : ArmState} {K : Nat} {G : BitVec 64 → Prop}
    (hRA : (L.act FA s0 K G).Wf) {x : ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : ArmState}
    (hq : Q (L.act FA s0 K G) x (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock}
    {info : CallInfo} (hvb : FA.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.call info))
    (hd : info.dest = .sym nB) :
    L.M x = enter FB x ∧ stepEvs x = [] ∧ cls x = .plain := by
  have hst := q_stRel hq
  obtain ⟨-, -, -, regs, i', -, -, -, -, -, -, -, -, -, -, -, hal, -, -, hasg, -⟩ :=
    q_op hq hvb hi
  obtain ⟨j, xx, t, hj, hx, hpc⟩ := callAt_of_q hq hvb hi call_hcall regs i' hal hasg
  obtain ⟨ic, rfl, hsym, -⟩ := assign_call hasg
  have hicd := hsym nB hd
  have hxx : xx = .bl nB := by
    simp only [MInst.callInsn?, hicd, Option.some.injEq] at hx
    exact hx.symm
  subst hxx
  obtain ⟨hstep, hev, hcls⟩ := CallSeg.step_bl hRA hj hst.prog hpc
  refine ⟨?_, hev, hcls⟩
  rw [M_eq_step hL hA hst.prog (not_isRet hL hA hj (by simp) hpc) s0 K G, hstep]
  exact H_call_some (find_eq hL hB) x

/-- **The callee's activation entered by the `bl`** (module doc). -/
theorem enter_call (hL : L.Ok) {nB : String} {FB : LFn} (hB : (nB, FB) ∈ L.fns)
    (hFB : FB.Static) {x : ArmState} (herr : Arm.r .ERR x = .None)
    (hal : Arm.CheckSPAlignment x)
    (hcode : ∀ k w, FB.fb.words[k]? = some w →
      Arm.read_mem_bytes 4 (FB.base + BitVec.ofNat 64 (4 * k)) x = w)
    {KB : Nat} {GB : BitVec 64 → Prop} (hstB : StackAvail KB FB.af (enter FB x))
    (hgB : ∀ a, GB a → ¬ StackBelow (frameDrop FB.af + KB) (spv (enter FB x)) a) :
    (L.act FB (enter FB x) KB GB).Wf ∧
      AbiCall FB.fb FB.base (Arm.r .PC x + 4#64) (enter FB x) ∧
      (∀ f, f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f (enter FB x) = Arm.r f x) ∧
      xreg 30 (enter FB x) = Arm.r .PC x + 4#64 ∧ (enter FB x).mem = x.mem ∧
      Q (L.act FB (enter FB x) KB GB)
        (iterN (L.act FB (enter FB x) KB GB).step (prologueLines FB.af.saves FB.af.frameSize FB.af.isCaller).length
          (enter FB x))
        (MConf.init FB.rf (locVal (L.act FB (enter FB x) KB GB).fr
          (iterN (L.act FB (enter FB x) KB GB).step (prologueLines FB.af.saves FB.af.frameSize FB.af.isCaller).length
            (enter FB x))) (bodyOf FB.af (enter FB x))) ∧
      AInv (L.act FB (enter FB x) KB GB)
        (MConf.init FB.rf (locVal (L.act FB (enter FB x) KB GB).fr
          (iterN (L.act FB (enter FB x) KB GB).step (prologueLines FB.af.saves FB.af.frameSize FB.af.isCaller).length
            (enter FB x))) (bodyOf FB.af (enter FB x))) := by
  have hRB : (L.act FB (enter FB x) KB GB).Wf := act_wf hFB hstB (enter_program FB x) hgB
  have hent : AbiCall FB.fb FB.base (Arm.r .PC x + 4#64) (enter FB x) := {
    program := enter_program FB x
    code k w hk := by
      rw [← hcode k w hk]
      exact read_mem_bytes_congr _ _ fun i _ => by rw [enter_mem]
    pc := enter_pc FB x
    err := by rw [r_enter (by simp) (by simp)]; exact herr
    lr := enter_x30 FB x
    spAligned := by
      have := (checkSP_iff x).1 hal
      show (Arm.r (.GPR 31#5) (enter FB x)).toNat % 16 = 0
      rw [r_enter (by simp) (by simp)]; exact this
    fits := (hL.laid _ hB).fit }
  obtain ⟨-, hq, hA⟩ := q_init_lines hRB hent
    ((Binary.bodyEntry_bodyOf FB.af (enter FB x)).w (L.act FB (enter FB x) KB GB).F
      hFB.entryArg)
  exact ⟨hRB, hent, fun f h1 h2 => r_enter h1 h2 FB x, enter_x30 FB x, enter_mem FB x, hq, hA⟩

end Link

end Concurrency.LinkedMachine
