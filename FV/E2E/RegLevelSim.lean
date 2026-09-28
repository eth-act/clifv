import FV.E2E.RegLevelMachine
import FV.Backend.Proof.RegallocLayout

/-!
# The register-level simulation relation (M6)

The Arm machine `ArmStepX` running the laid-out function realises the allocated code
(`MStep`) item by item. `Q R s c` relates an Arm state `s` to an allocated-code configuration
`c` of the activation `R`:

* **position**: the pc is at line `j` of the final line list, and the lines from `j` on are the
  `fallthrough` of the remaining items' lines (followed by the next block's label);
* **store**: every valid location (allocatable register, spill/save slot) holds in `s` what the
  store `m` says (`locVal`);
* **world**: `s` has the world `w` (`SameWorld (R.F)`: equal outside allocatable registers,
  x16/x17, the pc and the frame addresses), no error, the function's program, `sp` at the
  body's frame, fp/lr saved at the top of the frame.

Returns and traps are the last step of a run and are treated separately (their `Q` is `True`).
-/

namespace Backend.Proof

open Backend E2E

/-- The frame addresses of the activation entered in `s` (`lo`, `hi` = the frame's `intBase`,
`size`): the spill, save and float-move slots `[sp_body + lo, sp_body + hi)`, the padding and
fp/lr above the CLIF slots `[sp_body + frameSize, sp_entry)` (the explicit CLIF slots in between
belong to the world; empty without a frame), and the code words (read as data by jump tables;
the program never accesses them). -/
def frameF (lo hi : Nat) (af : AFunc) (s : Arm.ArmState) (a : BitVec 64) : Prop :=
  (lo ≤ (a - (spv s - BitVec.ofNat 64 (frameDrop af))).toNat ∧
    (a - (spv s - BitVec.ofNat 64 (frameDrop af))).toNat < hi) ∨
  (af.frameSize ≤ (a - (spv s - BitVec.ofNat 64 (frameDrop af))).toNat ∧
    (a - (spv s - BitVec.ofNat 64 (frameDrop af))).toNat < frameDrop af) ∨
  CodeAddr s a

/-- The fixed data of one activation. -/
structure RL where
  vc : VCode
  rf : RFunc
  af : AFunc
  fa : FnAsm
  fb : FnBin
  lm : Std.HashMap Lbl Nat
  base : BitVec 64
  /-- the ABI entry state -/
  s0 : Arm.ArmState
  X : ExtSem
  H : ArmHooks
  /-- the emitter's final state (trap table) -/
  psF : PState

namespace RL
variable (R : RL)

def fr : RAFrame := RAFrame.compute R.vc R.rf
def L : List Line := R.fa.lines.toList
def ctx : FnCtx := ⟨R.fa.k, R.af.slotBase⟩
/-- `sp` in the body. -/
def spB : BitVec 64 := spv R.s0 - BitVec.ofNat 64 (frameDrop R.af)
/-- The frame addresses. -/
def F : BitVec 64 → Prop := frameF R.fr.intBase R.fr.size R.af R.s0
/-- Address of line `j`. -/
def pcOf (j : Nat) : BitVec 64 := R.base + BitVec.ofNat 64 (lineOffset R.L j)
/-- The encoder's environment at line `j`. -/
def envOf (j : Nat) : Env := ⟨lineOffset R.L j, (R.lm[·]?)⟩
/-- The instruction semantics of the activation. -/
noncomputable def sem : ISem CV Arm.ArmState := csem R.F R.ctx R.X
/-- The machine. -/
noncomputable def step : Arm.ArmState → Arm.ArmState := ArmStepX R.X R.H R.fa

end RL

/-- The Arm state `s` represents store `m` and world `w`. -/
structure StRel (R : RL) (s : Arm.ArmState) (m : Loc → CV) (w : Arm.ArmState) : Prop where
  store : ∀ l, ValidLoc l → Live R.rf l → m l = locVal R.fr s l
  world : SameWorld R.F s w
  err : Arm.r .ERR s = .None
  prog : s.program = R.fb.program R.base
  sp : spOf s = R.spB
  align : Arm.CheckSPAlignment s
  /-- fp/lr as pushed by the prologue -/
  fplr : R.af.frame = true →
    Arm.read_mem_bytes 16 (spv R.s0 - 16#64) s = xreg 30 R.s0 ++ xreg 29 R.s0
  /-- the code words are readable as data -/
  code : ∀ k w, R.fb.words[k]? = some w →
    Arm.read_mem_bytes 4 (R.base + BitVec.ofNat 64 (4 * k)) s = w

/-- The checker accepts the remaining items of block `vb` (from VCode index `k`). -/
def ItemsChecked (R : RL) (vb : VBlock) (its : List RItem) : Prop :=
  ∃ (c : CheckCtx) (k : Nat) (a out : AState), c.rf = R.rf ∧ c.vc = R.vc ∧ c.runItems vb k its a = .ok out

/-- **The simulation relation.** -/
def Q (R : RL) (s : Arm.ArmState) : MConf CV Arm.ArmState → Prop
  | .run ⟨b, its, m, w⟩ =>
    ∃ j vb items pre code ls ps1 ps2 T,
      R.vc.blocks[b]? = some vb ∧ R.rf.blocks[b]? = some items ∧ items.toList = pre ++ its ∧
      ItemsChecked R vb its ∧
      itemsCode R.fr vb its = .ok code ∧
      codeLinesE R.ctx R.af code ps1 = .ok (ls, ps2) ∧
      ps2.traps.toList <+: R.psF.traps.toList ∧
      R.L.drop j = ftList (ls ++ nxtOf R.af b) ++ T ∧
      Arm.r .PC s = R.pcOf j ∧ StRel R s m w
  | _ => True

end Backend.Proof

namespace Backend.Proof

open Backend E2E

/-! ## Code bookkeeping -/

theorem mem_wordsAt {base : BitVec 64} :
    ∀ (ws : List (BitVec 32)) (k0 k : Nat) (w : BitVec 32), ws[k]? = some w →
      List.Mem (base + BitVec.ofNat 64 (4 * (k0 + k)), w) (wordsAt base k0 ws)
  | [], _, _, _, h => by simp at h
  | w' :: ws, k0, 0, w, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact List.Mem.head _
  | w' :: ws, k0, k + 1, w, h => by
    simp only [List.getElem?_cons_succ] at h
    have := mem_wordsAt (base := base) ws (k0 + 1) k w h
    rw [show k0 + 1 + k = k0 + (k + 1) by omega] at this
    exact List.Mem.tail _ this

/-- The bytes of code word `k` are code addresses of a state holding the function's program. -/
theorem codeAddr_word {s : Arm.ArmState} {base : BitVec 64} {fb : FnBin}
    (hp : s.program = fb.program base) {k : Nat} {w : BitVec 32} (hk : fb.words[k]? = some w)
    {i : Nat} (hi : i < 4) : CodeAddr s (base + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 i) := by
  refine ⟨(base + BitVec.ofNat 64 (4 * k), w), ?_, ?_⟩
  · rw [hp]
    have := mem_wordsAt (base := base) fb.words.toList 0 k w (by simpa using hk)
    rw [Nat.zero_add] at this
    exact this
  · simp only
    rw [show base + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 i - (base + BitVec.ofNat 64 (4 * k)) =
      BitVec.ofNat 64 i by bv_omega]
    simp only [BitVec.toNat_ofNat]
    omega

/-- The code words are kept by a step that keeps the memory at code addresses. -/
theorem code_keep {s0 s s' : Arm.ArmState} {base : BitVec 64} {fb : FnBin}
    (hp : s0.program = fb.program base)
    (hc : ∀ k w, fb.words[k]? = some w → Arm.read_mem_bytes 4 (base + BitVec.ofNat 64 (4 * k)) s = w)
    (hm : ∀ a, CodeAddr s0 a → s'.mem a = s.mem a) :
    ∀ k w, fb.words[k]? = some w → Arm.read_mem_bytes 4 (base + BitVec.ofNat 64 (4 * k)) s' = w := by
  intro k w hk
  rw [← hc k w hk]
  exact read_mem_bytes_congr _ _ fun i hi => hm _ (codeAddr_word hp hk hi)

theorem codeLinesE_append {c : FnCtx} {af : AFunc} :
    ∀ (A B : List AInst) (ps ps' : PState) (ls : List Line),
      codeLinesE c af (A ++ B) ps = .ok (ls, ps') →
      ∃ ls1 ls2 psm, codeLinesE c af A ps = .ok (ls1, psm) ∧
        codeLinesE c af B psm = .ok (ls2, ps') ∧ ls = ls1 ++ ls2
  | [], B, ps, ps', ls, h => ⟨[], ls, ps, rfl, by simpa using h, by simp⟩
  | a :: A, B, ps, ps', ls, h => by
    simp only [List.cons_append, codeLinesE, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r hr
      split at h
      · cases h
      · rename_i r2 hr2
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ls1, ls2, psm, h1, h2, h3⟩ := codeLinesE_append A B r.2 r2.2 r2.1 hr2
        refine ⟨r.1 ++ ls1, ls2, psm, ?_, h2, ?_⟩
        · simp [codeLinesE, bind, Except.bind, hr, h1, pure, Except.pure]
        · rw [h3]; simp

theorem itemsCode_cons {fr : RAFrame} {vb : VBlock} {it : RItem} {its : List RItem}
    {code : List AInst} (h : itemsCode fr vb (it :: its) = .ok code) :
    ∃ c1 c2, itemCode fr vb it = .ok c1 ∧ itemsCode fr vb its = .ok c2 ∧ code = c1 ++ c2 := by
  simp only [itemsCode, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i c1 h1
    split at h
    · cases h
    · rename_i c2 h2
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact ⟨c1, c2, h1, h2, h.symm⟩

theorem execLines_pc : ∀ {env : Env} {ls : List Line} {s s' : Arm.ArmState},
    execLines env ls s = some s' → Arm.r .PC s' = Arm.r .PC s + BitVec.ofNat 64 (4 * ls.length)
  | _, [], s, s', h => by simp [execLines] at h; subst h; simp
  | _, .label _ :: _, _, _, h => by simp [execLines] at h
  | _, .word _ _ :: _, _, _, h => by simp [execLines] at h
  | env, .ins i t :: ls, s, s', h => by
    simp only [execLines] at h
    split at h
    · split at h
      · rename_i hpc
        rw [execLines_pc h, hpc, BitVec.add_assoc]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]
        omega
      · cases h
    · cases h

/-- Lines of instructions only: each is 4 bytes. -/
theorem lineOffset_drop_ins {L : List Line} {j : Nat} {ls T : List Line}
    (hd : L.drop j = ls ++ T) (hins : ∀ ln ∈ ls, ∃ i t, ln = .ins i t) :
    lineOffset L (j + ls.length) = lineOffset L j + 4 * ls.length := by
  induction ls generalizing j with
  | nil => simp
  | cons ln ls ih =>
    obtain ⟨i, t, rfl⟩ := hins ln (by simp)
    have hj : L[j]? = some (.ins i t) := by
      have := congrArg (·[0]?) hd
      simpa [List.getElem?_drop] using this
    have hd' : L.drop (j + 1) = ls ++ T := by
      rw [← List.drop_drop, hd]; rfl
    have := ih hd' (fun x hx => hins x (by simp [hx]))
    have h1 := lineOffset_succ L j _ hj
    simp only [Line.size] at h1
    simp only [List.length_cons]
    rw [show j + (ls.length + 1) = j + 1 + ls.length by omega, this, h1]
    omega

end Backend.Proof
