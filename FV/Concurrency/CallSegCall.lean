import FV.Concurrency.CallEntryLink
import FV.Concurrency.FrameDisj
import FV.Concurrency.CallValid
import FV.Concurrency.CallRetLink

/-!
# The call pause of a compiled activation: entering the callee and resuming after it (#473)

`Link.call_end` enters a callee `FB` from a caller's paused `call` given three facts about the
callee's activation: its code words in memory (`hcode`), its stack budget (`hstB`) and its kept
addresses outside its region (`hgB`). Here they come from the caller:

* **`CodeIn L R`**: every word of every linked function lies in `R`'s kept addresses and is in
  memory at `R`'s entry; `CodeIn.code` reads them back at any state related to `R` (`gkeep`),
  `CodeIn.callee` passes `CodeIn` on to a callee keeping the caller's frame and kept addresses
  (`G = R.FK`);
* **`stackAvail_callee`**: a callee entered at the caller's body `sp` with budget `KB` has its
  `StackAvail` when `frameSize + 16 + KB` fits in the caller's budget and `KB` covers its stack
  probes below its frame (`probeBelow`, #581; `stackRoom_callee` without them; the linked code is
  in the caller's kept addresses, so outside its region); **`budget_call`**: with a budget
  `(Dcap - d) * M` at depth `d < Dcap` (`M` bounding every `frameSize + 16`), the callee's budget
  `K - (frameSize + 16)` is `(Dcap - (d + 1)) * M` or more;
* `nested_callee`: that callee is `Nested` in its caller; **`gfree_callee`**: its kept
  addresses `R.FK` avoid its region (`Nested.region_not_FK`);
* **`call_endK`**: `Link.call_end` with these three premises discharged, the callee's
  `CodeIn` and nesting added to its conclusion;
* `retEnd_n`: a callee's `RetEnd` holds at every step count reaching the return address without
  error (the first step outside the code: `stuck_outside`);
* **`resume_ret`**: `CallArity.resume_allA` with the callee's memory relation (`hB`), the bytes
  outside its world (`hmemB`), its result registers (`hus`, `hpreB`) and the return state (`hy`,
  `hprog`) from its `RetEnd`, and the valid ranges (`hval`) from `CallValid.AllocInvD` of the
  CLIF state after the return (`valid_of_allocInvD`).
-/

namespace Concurrency.CallSegCall

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread AllocThread IselCheck ThreadRefine IselCall IselCallRet ArmAllocThread E2E
  ClifCStepTerm IselThread CallRetsEnd LinkedMachine LinkedMachine.Link CallArgsL2
  CallArgsEntry CallArgsAt CallResumeChecks FrameDisj ArmFoot ArmInstFoot

variable {L : Link}

/-! ## The linked code, kept -/

/-- **The link's code is kept by `R`** (module doc): every linked function is `R`'s own (its
code is in `R`'s program) or its words lie in `R`'s kept addresses and are in memory at `R`'s
entry. -/
def CodeIn (L : Link) (R : RL) : Prop :=
  ∀ n FB, (n, FB) ∈ L.fns → (FB.fb = R.fb ∧ FB.base = R.base) ∨
    ∀ k wd, FB.fb.words[k]? = some wd →
      (∀ i < 4, R.G (FB.base + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 i)) ∧
      Arm.read_mem_bytes 4 (FB.base + BitVec.ofNat 64 (4 * k)) R.s0 = wd

/-- **The linked code at a state related to `R`** (its own code by `StRel.code`, the others' by
`gkeep`). -/
theorem CodeIn.code {R : RL} (h : CodeIn L R) {x : ArmState} {m : Loc → CV} {w : ArmState}
    (hS : StRel R x m w) {n : String} {FB : LFn} (hB : (n, FB) ∈ L.fns) :
    ∀ k wd, FB.fb.words[k]? = some wd →
      Arm.read_mem_bytes 4 (FB.base + BitVec.ofNat 64 (4 * k)) x = wd := by
  intro k wd hk
  rcases h n FB hB with ⟨hfb, hbase⟩ | h'
  · rw [hfb] at hk; rw [hbase]; exact hS.code k wd hk
  · obtain ⟨hG, h0⟩ := h' k wd hk
    rw [← h0]
    exact read_mem_bytes_congr 4 _ fun i hi => hS.gkeep _ (hG i hi)

/-- **A callee keeping the caller's frame and kept addresses keeps the linked code.** -/
theorem CodeIn.callee {A : RL} (h : CodeIn L A) (hA : A.Wf) {x : ArmState} {m : Loc → CV}
    {w : ArmState} (hS : StRel A x m w) (F : LFn) (KB : Nat) :
    CodeIn L (L.act F (enter F x) KB A.FK) := fun n FB hB => by
  by_cases ho : FB.fb = F.fb ∧ FB.base = F.base
  · exact .inl ho
  refine .inr fun k wd hk => ⟨fun i hi => ?_, ?_⟩
  · rcases h n FB hB with ⟨hfb, hbase⟩ | h'
    · refine Or.inl (Or.inr (Or.inr ?_))
      rw [hbase]
      rw [hfb] at hk
      exact codeAddr_word hA.prog0 hk hi
    · exact Or.inr ((h' k wd hk).1 i hi)
  · show Arm.read_mem_bytes 4 _ (enter F x) = wd
    rw [← h.code hS hB k wd hk]
    exact read_mem_bytes_congr 4 _ fun i _ => by rw [enter_mem]

theorem wordsAt_addr {base : BitVec 64} : ∀ {k : Nat} {ws : List (BitVec 32)}
    {p : BitVec 64 × BitVec 32}, List.Mem p (wordsAt base k ws) →
    ∃ j < ws.length, p.1 = base + BitVec.ofNat 64 (4 * (k + j))
  | _, [], _, h => nomatch h
  | k, w :: ws, p, h => by
    cases h with
    | head => exact ⟨0, by simp, rfl⟩
    | tail _ h =>
      obtain ⟨j, hj, he⟩ := wordsAt_addr h
      exact ⟨j + 1, by simp; omega, by rw [he]; congr 3; omega⟩

/-- A code address of a state holding a function's program is in one of its words. -/
theorem codeAddr_words {s : ArmState} {base a : BitVec 64} {fb : FnBin}
    (hp : s.program = fb.program base) (h : CodeAddr s a) :
    ∃ j < fb.words.size, (a - (base + BitVec.ofNat 64 (4 * j))).toNat < 4 := by
  obtain ⟨p, hp', hd⟩ := h
  rw [hp] at hp'
  obtain ⟨j, hj, he⟩ := wordsAt_addr hp'
  simp only [Nat.zero_add] at he
  exact ⟨j, by simpa using hj, by rw [← he]; exact hd⟩

/-- **The code addresses of a linked function avoid `R`'s region.** -/
theorem CodeIn.notRegion {R : RL} (h : CodeIn L R) (hR : R.Wf) {n : String} {FB : LFn}
    (hB : (n, FB) ∈ L.fns) {s : ArmState} (hp : s.program = FB.fb.program FB.base)
    {a : BitVec 64} (ha : CodeAddr s a) : ¬ StackBelow (frameDrop R.af + R.K) (spv R.s0) a := by
  rcases h n FB hB with ⟨hfb, hbase⟩ | h'
  · have hc : CodeAddr R.s0 a := by
      unfold CodeAddr at ha ⊢
      rwa [hR.prog0, ← hfb, ← hbase, ← hp]
    exact code_not_region hR hc
  obtain ⟨j, hj, hd⟩ := codeAddr_words hp ha
  have hG := (h' j _ (Array.getElem?_eq_getElem hj)).1 _ hd
  have e : FB.base + BitVec.ofNat 64 (4 * j) +
      BitVec.ofNat 64 (a - (FB.base + BitVec.ofNat 64 (4 * j))).toNat = a := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
  rw [e] at hG
  exact hR.gfree a hG

/-! ## The callee's stack -/

theorem spv_enter {A : RL} {x : ArmState} {m : Loc → CV} {w : ArmState} (hS : StRel A x m w)
    (F : LFn) : spv (enter F x) = A.spB := by
  show Arm.r (.GPR 31#5) (enter F x) = _
  rw [r_enter (by simp) (by simp)]
  exact hS.sp

/-- **The callee's stack room**: the callee's frame and budget below its entry `sp` hold no
code (`StackAvail` without its probe budget, #581). -/
theorem stackRoom_callee {A : RL} (hA : A.Wf) {x : ArmState} {m : Loc → CV} {w : ArmState}
    (hS : StRel A x m w) (hc : CodeIn L A) {n : String} {FB : LFn} (hB : (n, FB) ∈ L.fns)
    {KB : Nat} (hK : FB.af.frameSize + 16 + KB ≤ A.K) :
    StackRoom (FB.af.frameSize + 16 + KB) (enter FB x) := by
  have hsp := spv_enter hS FB
  obtain ⟨h1, h2⟩ := spB_toNat hA
  have hspB : A.spB = spv A.s0 - BitVec.ofNat 64 (frameDrop A.af) := rfl
  refine ⟨?_, fun a ha => ?_⟩
  · rw [hsp]; omega
  · have hnot := hc.notRegion hA hB (enter_program FB x) ha
    rw [hsp]
    unfold StackBelow at hnot
    generalize FB.af.frameSize + 16 + KB = N at hK ⊢
    generalize frameDrop A.af = d at h1 h2 hspB hnot
    generalize A.K = K at h2 hK hnot
    generalize spv A.s0 = s at h1 h2 hspB hnot
    generalize A.spB = b at h1 hspB ⊢
    subst hspB
    bv_omega

/-- **The callee's stack** (module doc). (#581: `hp`, the callee's probes below its frame within
its budget, is new: `StackAvail` now also bounds them, so without it the statement is false for
a calling callee whose probed stack is a multiple of 4 KiB.) -/
theorem stackAvail_callee {A : RL} (hA : A.Wf) {x : ArmState} {m : Loc → CV} {w : ArmState}
    (hS : StRel A x m w) (hc : CodeIn L A) {n : String} {FB : LFn} (hB : (n, FB) ∈ L.fns)
    {KB : Nat} (hK : FB.af.frameSize + 16 + KB ≤ A.K) (hp : probeBelow FB.af ≤ KB) :
    StackAvail KB FB.af (enter FB x) :=
  ⟨stackRoom_callee hA hS hc hB hK, hp⟩

/-- **The callee's budget at depth `d` below `Dcap`** (module doc). -/
theorem budget_call {Dcap d M K N : Nat} (hK : (Dcap - d) * M ≤ K) (hd : d < Dcap)
    (hN : N ≤ M) : N ≤ K ∧ (Dcap - (d + 1)) * M ≤ K - N := by
  obtain ⟨e, he⟩ : ∃ e, Dcap - d = e + 1 := ⟨Dcap - d - 1, by omega⟩
  have he' : Dcap - (d + 1) = e := by omega
  rw [he, Nat.succ_mul] at hK
  rw [he']
  omega

/-- **The callee is nested in its caller.** -/
theorem nested_callee {A : RL} {x : ArmState} {m : Loc → CV} {w : ArmState}
    (hS : StRel A x m w) {FB : LFn} {KB : Nat} (hK : frameDrop FB.af + KB ≤ A.K) :
    Nested A (L.act FB (enter FB x) KB A.FK) where
  sp_le := by show (spv (enter FB x)).toNat ≤ _; rw [spv_enter hS]; exact Nat.le_refl _
  fits := by
    show A.spB.toNat + (frameDrop FB.af + KB) ≤ (spv (enter FB x)).toNat + A.K
    rw [spv_enter hS]; omega
  keep := rfl

/-- **The callee's kept addresses avoid its region** (module doc). -/
theorem gfree_callee {A : RL} (hA : A.Wf) {x : ArmState} {m : Loc → CV} {w : ArmState}
    (hS : StRel A x m w) (hc : CodeIn L A) {n : String} {FB : LFn} (hB : (n, FB) ∈ L.fns)
    {KB : Nat} (hK : FB.af.frameSize + 16 + KB ≤ A.K) :
    ∀ a, A.FK a → ¬ StackBelow (frameDrop FB.af + KB) (spv (enter FB x)) a := fun a hG hR =>
  (nested_callee (L := L) hS (by have := frameDrop_le FB.af; omega)).region_not_FK_room hA
    (stackRoom_callee hA hS hc hB hK) hR hG

/-! ## The call end -/

/-- **`Link.call_end` from the caller's kept code and budget** (module doc). (#581: `hpB`, the
callee's probes below its frame within its budget `KB`, is new: the callee's `R.Wf` includes
`StackAvail`, which now bounds them.) -/
theorem call_endK (hL : L.Ok) {nA : String} {FA : LFn} (hA : (nA, FA) ∈ L.fns) {s0 : ArmState}
    {K : Nat} {G : BitVec 64 → Prop} (hRA : (L.act FA s0 K G).Wf)
    (hcin : CodeIn L (L.act FA s0 K G))
    {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
    {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {Γ : E2E.Rel}
    {c : BitVec 64} {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}
    (H : DriverHypT f vc ctx st0 R gn bl A
      (csem (L.act FA s0 K G).F (L.act FA s0 K G).ctx (L.act FA s0 K G).X) (RelW Γ f c) env p)
    (hchk : threadCheckBlC f bl = true) (hres : callResLenB f = true)
    (hcu : callUseRegsBl f bl = true)
    (hlow : lowerCheck f vc = true) (hind : indSigs f = []) (hv : verifiable f = true)
    (hnt : f.blocks.all (fun B => !B.term.isTry) = true) (hout0 : vc.outgoing = 0)
    (hslot : (L.act FA s0 K G).ctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → (L.act FA s0 K G).X.sym n 0 = BitVec.ofNat 64 b)
    (hX0 : NoCall (L.act FA s0 K G).X)
    {Lp : Nat → Prop} {ss ss' : Array (Array Nat)} (H3 : PrepFacts vc (L.act FA s0 K G).vc Lp ss ss')
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt (L.act FA s0 K G).vc (L.act FA s0 K G).rf cc ins a0) {r₀ : Reg → CV}
    (huv : CallUsesVirt (L.act FA s0 K G).vc) (hdv : CallDefsVirt (L.act FA s0 K G).vc)
    {x : ArmState} {s' : Clif.State} {vV' vP' : VState CV ArmState} {cM' : MState CV ArmState}
    (hq : Q (L.act FA s0 K G) x (.run cM')) (hP : Pause (L.act FA s0 K G) (.run cM'))
    (hm2 : Match f ctx R gn bl A (RelW Γ f c) slots s' vV')
    (hm3 : PMatch vc (L.act FA s0 K G).vc
      (csem (L.act FA s0 K G).F (L.act FA s0 K G).ctx (L.act FA s0 K G).X)
      (cEvs (L.act FA s0 K G).F (L.act FA s0 K G).ctx) Lp ss' (.run vV') (.run vP'))
    (hm4 : MatchRun cc ins ckeep r₀ cM' vP')
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s'.frame.body = stm :: rest)
    {fn : Clif.FnRef} {args : List Clif.ValueId} (hcl : stm.inst = .call fn args)
    {ext : Clif.ExtFunc} (hext : s'.frame.func.extern? fn = some ext)
    (huniq : ∀ e ∈ f.externs, e.2.name = ext.name → e.2 = ext)
    {vals : List Clif.Val} (hvals : s'.frame.getMany args = .ok vals)
    (htys : vals.map (·.ty) = Clif.AbiParam.tys ext.sig.params)
    {FB : LFn} (hB : (ext.name, FB) ∈ L.fns) (hFB : FB.Static)
    {KB : Nat} (hKB : FB.af.frameSize + 16 + KB ≤ K) (hpB : probeBelow FB.af ≤ KB)
    {fB : Clif.Function} (hsig : fB.sig = ext.sig) :
    L.M x = enter FB x ∧ stepEvs x = [] ∧ cls x = .plain ∧
      (L.act FB (enter FB x) KB (L.act FA s0 K G).FK).Wf ∧
      AbiCall FB.fb FB.base (Arm.r .PC x + 4#64) (enter FB x) ∧
      (∀ f, f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f (enter FB x) = Arm.r f x) ∧
      xreg 30 (enter FB x) = Arm.r .PC x + 4#64 ∧ (enter FB x).mem = x.mem ∧
      Q (L.act FB (enter FB x) KB (L.act FA s0 K G).FK)
        (iterN (L.act FB (enter FB x) KB (L.act FA s0 K G).FK).step
          (prologueLines FB.af.saves FB.af.frameSize FB.af.isCaller).length (enter FB x))
        (MConf.init FB.rf (locVal (L.act FB (enter FB x) KB (L.act FA s0 K G).FK).fr
          (iterN (L.act FB (enter FB x) KB (L.act FA s0 K G).FK).step
            (prologueLines FB.af.saves FB.af.frameSize FB.af.isCaller).length (enter FB x))) (bodyOf FB.af (enter FB x))) ∧
      AInv (L.act FB (enter FB x) KB (L.act FA s0 K G).FK)
        (MConf.init FB.rf (locVal (L.act FB (enter FB x) KB (L.act FA s0 K G).FK).fr
          (iterN (L.act FB (enter FB x) KB (L.act FA s0 K G).FK).step
            (prologueLines FB.af.saves FB.af.frameSize FB.af.isCaller).length (enter FB x))) (bodyOf FB.af (enter FB x))) ∧
      ArgsAtEntry (L.act FB (enter FB x) KB (L.act FA s0 K G).FK).F fB.sig vals
        (bodyOf FB.af (enter FB x)) ∧
      CodeIn L (L.act FB (enter FB x) KB (L.act FA s0 K G).FK) ∧
      Nested (L.act FA s0 K G) (L.act FB (enter FB x) KB (L.act FA s0 K G).FK) := by
  have hst := q_stRel hq
  have hK' : frameDrop FB.af + KB ≤ K := by have := frameDrop_le FB.af; omega
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := call_end hL hA hRA H hchk hres hcu hlow
    hind hv hnt hout0 hslot hsym hX0 H3 hc huv hdv hq hP hm2 hm3 hm4 hbody hcl hext huniq hvals
    htys hB hFB (hcin.code hst hB) (stackAvail_callee hRA hst hcin hB hKB hpB)
    (gfree_callee hRA hst hcin hB hKB) hsig
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hcin.callee hRA hst FB KB,
    nested_callee hst hK'⟩

/-! ## The resume after the callee -/

/-- No two step counts `a < b` with the return address (outside the code) at `a` and no error at
`b`: the machine is stuck outside the code. -/
theorem ret_lt {R : RL} (hR : R.Wf) {ra : BitVec 64}
    (hra : ∀ k < R.fb.words.size, ra ≠ R.base + BitVec.ofNat 64 (4 * k)) {x : ArmState}
    {a b : Nat} (hab : a < b) (hprog : (iterN R.step a x).program = R.fb.program R.base)
    (hpc : Arm.r .PC (iterN R.step a x) = ra) (herr : Arm.r .ERR (iterN R.step b x) = .None) :
    False := by
  have hs := stuck_outside hR (t := iterN R.step a x) hprog (by rw [hpc]; exact hra)
    (b - a - 1)
  rw [← iterN_add, show a + (b - a - 1 + 1) = b by omega] at hs
  exact hs herr

/-- **A callee's `RetEnd` at every step count reaching its return address without error**
(module doc). The relation at the `rets` pause is `RetEnd`'s `QA` (in a return tail after the
callee restores, which emit no code, the store differs from the machine at the restored
registers). -/
theorem retEnd_n {R : RL} (hR : R.Wf) {ra : BitVec 64} (hent : AbiCall R.fb R.base ra R.s0)
    (hra : ∀ k < R.fb.words.size, ra ≠ R.base + BitVec.ofNat 64 (4 * k))
    {env : Clif.Env} {p : Clif.Program} {MR : MemRelT} {slots : List (Clif.SlotId × Nat)}
    {r₀ : Reg → CV} {x : ArmState} {s' : Clif.State} (hret : RetEnd R ra env p MR slots r₀ x s')
    {n : Nat} (hpc : Arm.r .PC (iterN R.step n x) = ra)
    (herr : Arm.r .ERR (iterN R.step n x) = .None) :
    ∃ b k allocs its m w vb us ops ρ vals cm,
      QA R x (.run ⟨b, .op k allocs :: its, m, w⟩) ∧ R.vc.blocks[b]? = some vb ∧
      vb.insts[k]? = some (.rets us) ∧ (MInst.rets us).operands = .ok ops ∧
      Clif.step env p s' = .done vals cm ∧ PrefixHold vals (vuses ops ρ) ∧ MR slots s'.mem w ∧
      cm = (s'.mem.free (slots.map (·.2))).leave ∧ (iterN R.step n x).mem = x.mem ∧
      ∀ (j : Nat) (v q : Reg) (y : CV), us[j]? = some (v, q) → (vuses ops ρ)[j]? = some y →
        regVal (iterN R.step n x) q = y := by
  obtain ⟨n2, hpath, hRC2, -, hprog2, -, -, -, hret⟩ := retEnd_privP hR hent hra hret
  obtain ⟨b, k, allocs, its, m, w, vb, us, ops, ρ, vals, cm, n1, hq, hvb, hi, hops, hdone, hpre,
    hMR, hcm, -, hpc1, herr1, -, hmem1, ⟨hprog1, -⟩, -, hus⟩ := hret
  have hxp : x.program = R.fb.program R.base := (q_stRel (qa_q hq).choose_spec).prog
  have heq : ∀ n', Arm.r .PC (iterN R.step n' x) = ra → Arm.r .ERR (iterN R.step n' x) = .None →
      n' = n2 := fun n' hp he => by
    rcases Nat.lt_trichotomy n' n2 with h | h | h
    · exact (ret_lt hR hra h (hpath n' h).2.1 hp hRC2.2.1).elim
    · exact h
    · exact (ret_lt hR hra h (by rw [hprog2, hxp]) hRC2.1 he).elim
  obtain rfl := heq n hpc herr
  obtain rfl := heq n1 hpc1 herr1
  exact ⟨b, k, allocs, its, m, w, vb, us, ops, ρ, vals, cm, hq, hvb, hi, hops, hdone, hpre, hMR,
    hcm, hmem1, hus⟩

/-- **The caller resumed after its callee's return** (module doc). -/
theorem resume_ret {RA RB : RL} (hRA : RA.Wf) (hRB : RB.Wf) (hgv : RA.gv = fun _ _ => False)
    (hX0 : NoCall RA.X) {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    {Γ : E2E.Rel} {c : BitVec 64} {env : Clif.Env} {p : Clif.Program}
    {slots : List (Clif.SlotId × Nat)}
    (H : DriverHypT f vc ctx st0 R gn bl A (csem RA.F RA.ctx RA.X) (RelW Γ f c) env p)
    (hchk : threadCheckBlC f bl = true) (har : CallArity.callArityBl f bl = true)
    (hlow : lowerCheck f vc = true) (hind : indSigs f = [])
    (hv : verifiable f = true) (hnt : f.blocks.all (fun B => !B.term.isTry) = true)
    (hout0 : vc.outgoing = 0) (hΓF : Γ.F = RA.F) (hslot : RA.ctx.slotBase = Γ.slotOff)
    (hsym : ∀ n b, Γ.syms n = some b → RA.X.sym n 0 = BitVec.ofNat 64 b)
    {Lp : Nat → Prop} {ss ss' : Array (Array Nat)} (H3 : PrepFacts vc RA.vc Lp ss ss')
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (hc : CheckedAt RA.vc RA.rf cc ins a0) {r₀ : Reg → CV}
    (hvdef : CallDefsVirt RA.vc)
    {x : ArmState} {s' : Clif.State} {vV' vP' : VState CV ArmState} {cM' : MState CV ArmState}
    (hq : Q RA x (.run cM')) (hA : AInv RA (.run cM')) (hP : Pause RA (.run cM'))
    (hat : AtCallS s') (hm2 : Match f ctx R gn bl A (RelW Γ f c) slots s' vV')
    (hm3 : PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) Lp ss' (.run vV') (.run vP'))
    (hm4 : MatchRun cc ins ckeep r₀ cM' vP')
    {ra : BitVec 64} (hent : AbiCall RB.fb RB.base ra RB.s0)
    (hra : ∀ k < RB.fb.words.size, ra ≠ RB.base + BitVec.ofNat 64 (4 * k))
    (hfx : ∀ f, f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f RB.s0 = Arm.r f x)
    (hlr : xreg 30 RB.s0 = Arm.r .PC x + 4#64)
    (hm0 : ∀ a, RA.FK a → RB.s0.mem a = x.mem a) (hG : ∀ a, RA.FK a → RB.G a)
    {r₀B : Reg → CV}
    (hr₀B : ∀ r ∈ calleeSaved, ckeep r (r₀B r) =
      ckeep r (locVal RB.fr (iterN RB.step (prologueLines RB.af.saves RB.af.frameSize RB.af.isCaller).length RB.s0) (.reg r)))
    (hdr : ∀ (b : Nat) (vb : VBlock) (us : List (Reg × Reg)), RB.vc.blocks[b]? = some vb →
      (∃ k : Nat, vb.insts[k]? = some (MInst.rets us)) →
      CallDefsRet RA.vc (us.map (·.2)))
    {ΓB : E2E.Rel} {fB : Clif.Function} {cB : BitVec 64} {slotsB : List (Clif.SlotId × Nat)}
    {xB : ArmState} {sR : Clif.State}
    (hret : RetEnd RB ra env p (RelW ΓB fB cB) slotsB r₀B xB sR)
    (hΓB : ΓB.F = RB.F) (hsyms : ΓB.syms = Γ.syms)
    {n : Nat} (hy : RetC RB ra r₀B (iterN RB.step n xB))
    {rvals : List Clif.Val} {cmR : Clif.Mem} (hdone : Clif.step env p sR = .done rvals cmR)
    {d : Nat} {sRet : Clif.State} (hD : CallValid.AllocInvD s'.mem d sRet)
    (hd : sRet.callers.length = d) (hmR : sRet.mem = cmR)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s'.frame.body = stm :: rest)
    {fn : Clif.FnRef} {args : List Clif.ValueId} (hcl : stm.inst = .call fn args)
    {ext : Clif.ExtFunc} (hext : s'.frame.func.extern? fn = some ext)
    (huniq : ∀ e ∈ f.externs, e.2.name = ext.name → e.2 = ext)
    {vals : List Clif.Val} (hvals : s'.frame.getMany args = .ok vals)
    (htys : vals.map (·.ty) = Clif.AbiParam.tys ext.sig.params)
    (hrty : rvals.map (·.ty) = Clif.AbiParam.tys ext.sig.returns)
    {regs' : Clif.Regs} (hregs : s'.frame.regs.setMany stm.results rvals = some regs') :
    ∃ vV'' vP'' cM'',
      Match f ctx R gn bl A (RelW Γ f c) slots { s' with
          frame := { s'.frame with regs := regs', body := rest }, mem := cmR } vV'' ∧
      PMatch vc RA.vc (csem RA.F RA.ctx RA.X) (cEvs RA.F RA.ctx) Lp ss' (.run vV'') (.run vP'') ∧
      MatchRun cc ins ckeep r₀ cM'' vP'' ∧
      Q RA (set_program (iterN RB.step n xB) (RA.fb.program RA.base)) (.run cM'') ∧
      AInv RA (.run cM'') := by
  obtain ⟨b, k, allocs, its, m, w, vb, us, ops, ρ, vals', cm, hqaB, hvb, hi, -, hdone', hpre, hMR,
    hcm, hmem, hus⟩ := retEnd_n hRB hent hra hret hy.1 hy.2.1
  obtain ⟨mtB, hqB⟩ := qa_q hqaB
  rw [hdone] at hdone'
  cases hdone'
  have hxp : x.program = RA.fb.program RA.base := (q_stRel hq).prog
  have hB : MemRel RB.F Γ.syms sR.mem w := hΓB ▸ hsyms ▸ hMR.1.1
  have hy' : RetC RB ra r₀B (set_program (iterN RB.step n xB) (RA.fb.program RA.base)) := by
    obtain ⟨h1, h2, h3, h4, h29, h5⟩ := hy
    refine ⟨by rw [r_set_program]; exact h1, by rw [r_set_program]; exact h2, ?_, h4, ?_, ?_⟩
    · show Arm.r _ _ = _; rw [r_set_program]; exact h3
    · show Arm.r _ _ = _; rw [r_set_program]; exact h29
    · intro r hr; rw [regVal_set_program]; exact h5 r hr
  obtain ⟨vV'', vP'', cM'', h1, h2, h3, h4, h5⟩ := CallArity.resume_allA hRA hRB hgv hX0 H hchk
    har hlow hind hv hnt hout0 hΓF hslot hsym H3 hc hvdef hq hA hP hat hm2 hm3 hm4 hent hy' hfx
    hlr hm0 hG hr₀B (by rw [program_set_program, hxp]) (usB := us) (ysB := vuses ops ρ)
    (fun j v q u h1 h2 => by rw [regVal_set_program]; exact hus j v q u h1 h2) hpre
    (hdr b vb us hvb ⟨k, hi⟩) hB (bases := slotsB.map (·.2))
    (fun a k' hv' => CallValid.valid_of_allocInvD hD hd a k' (by rw [hmR, hcm]; exact hv'))
    (fun a ha => by
      rw [mem_set_program, hmem]; exact (q_stRel hqB).world.2.1 a ha)
    hbody hcl hext huniq hvals htys hrty hregs
  rw [← hcm] at h1
  exact ⟨vV'', vP'', cM'', h1, h2, h3, h4, h5⟩
end Concurrency.CallSegCall
