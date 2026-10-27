import FV.Backend.SkipDead
import FV.Backend.Proof.LowerSim

/-!
# Deleting instructions from a VCode (`deleteWith`)

`deleteWith vc mask` keeps the instructions of block `b` at the `true` positions of `mask b`. If
the mask fits, keeps every block's last instruction and the CFG, and no kept instruction or
branch argument reads a vreg in `G` (`Deletes vc vcK mask G`), then a run of `vc` that executes
only kept instructions (`StarP` with a predicate implying the mask) is a run of `vcK`, from and
to corresponding configurations (`CorrC`: same block and world, position `kidx` of the kept
ones, register files equal outside `G`): `starP_deletes`, and for traps and returns
`VTrapFromP.deletes`, `VRetFromP.deletes`.
-/

namespace Backend.Proof.Driver
open Backend Backend.Proof

/-! ## Masks -/

/-- The position in the masked list of position `k`: the kept positions before `k`. -/
def kidx (mask : List Bool) (k : Nat) : Nat := (mask.take k).count true

@[simp] theorem kidx_zero (mask : List Bool) : kidx mask 0 = 0 := by simp [kidx]

theorem kidx_succ {mask : List Bool} {k : Nat} {x : Bool} (h : mask[k]? = some x) :
    kidx mask (k + 1) = kidx mask k + (if x then 1 else 0) := by
  unfold kidx
  rw [List.take_add_one, h]
  cases x <;> simp [List.count_append]

theorem kidx_mono {mask : List Bool} {k k' : Nat} (h : k ≤ k') : kidx mask k ≤ kidx mask k' := by
  unfold kidx
  apply List.Sublist.count_le
  exact (List.take_prefix_take_left h).sublist

theorem kidx_le_count (mask : List Bool) (k : Nat) : kidx mask k ≤ mask.count true :=
  List.Sublist.count_le _ (List.take_sublist _ _)

theorem kidx_length (mask : List Bool) : kidx mask mask.length = mask.count true := by
  simp [kidx]

/-- Positions that are all deleted do not move the kept index. -/
theorem kidx_false_range {mask : List Bool} {k0 : Nat} :
    ∀ {len : Nat}, (∀ t < len, mask[k0 + t]? = some false) → kidx mask (k0 + len) = kidx mask k0
  | 0, _ => rfl
  | len + 1, h => by
    rw [← Nat.add_assoc, kidx_succ (h len (by omega)), kidx_false_range (fun t ht => h t (by omega))]
    rfl

/-- Positions that are all kept move the kept index along. -/
theorem kidx_true_range {mask : List Bool} {k0 : Nat} :
    ∀ {len : Nat}, (∀ t < len, mask[k0 + t]? = some true) →
      kidx mask (k0 + len) = kidx mask k0 + len
  | 0, _ => rfl
  | len + 1, h => by
    rw [← Nat.add_assoc, kidx_succ (h len (by omega)), kidx_true_range (fun t ht => h t (by omega))]
    simp; omega

theorem maskKeep_cons (x : Bool) (mask : List Bool) (m : MInst) (ms : List MInst) :
    maskKeep (x :: mask) (m :: ms) = (if x then [m] else []) ++ maskKeep mask ms := by
  cases x <;> simp [maskKeep]

theorem length_maskKeep {mask : List Bool} {ms : List MInst} (h : mask.length = ms.length) :
    (maskKeep mask ms).length = mask.count true := by
  induction ms generalizing mask with
  | nil => cases mask with
    | nil => rfl
    | cons _ _ => simp at h
  | cons m ms ih => cases mask with
    | nil => simp at h
    | cons x mask =>
      rw [maskKeep_cons, List.length_append, ih (by simpa using h)]
      cases x <;> simp <;> omega

theorem maskKeep_getElem? {mask : List Bool} {ms : List MInst} {k : Nat}
    (hl : mask.length = ms.length) (h : mask[k]? = some true) :
    (maskKeep mask ms)[kidx mask k]? = ms[k]? := by
  induction ms generalizing mask k with
  | nil => cases mask with
    | nil => simp at h
    | cons _ _ => simp at hl
  | cons m ms ih => cases mask with
    | nil => simp at h
    | cons x mask =>
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        subst h
        simp [maskKeep_cons]
      | succ k =>
        simp only [List.getElem?_cons_succ] at h
        have ih' := ih (mask := mask) (k := k) (by simpa using hl) h
        have hk : kidx (x :: mask) (k + 1) = (if x then 1 else 0) + kidx mask k := by
          cases x <;> simp [kidx] <;> omega
        rw [maskKeep_cons, hk, List.getElem?_cons_succ]
        cases x
        · simpa using ih'
        · simp only [ite_true, List.singleton_append]
          rw [Nat.add_comm, List.getElem?_cons_succ]; exact ih'

/-- A kept position that is not the last one is followed by a kept position, if the last one is
kept. -/
theorem kidx_next_lt {mask : List Bool} {k : Nat} (hk : mask[k]? = some true)
    (hlast : mask.getLast? = some true) (hlt : k + 1 < mask.length) :
    kidx mask k + 1 < mask.count true := by
  have h1 : kidx mask (k + 1) = kidx mask k + 1 := by rw [kidx_succ hk]; rfl
  have hl : mask[mask.length - 1]? = some true := by
    rw [← List.getLast?_eq_getElem?]; exact hlast
  have h2 : kidx mask (mask.length - 1 + 1) = kidx mask (mask.length - 1) + 1 := by
    rw [kidx_succ hl]; rfl
  have h3 := kidx_mono (mask := mask) (show k + 1 ≤ mask.length - 1 by omega)
  rw [show mask.length - 1 + 1 = mask.length by omega, kidx_length] at h2
  omega

theorem kidx_last_eq {mask : List Bool} {k : Nat} (hk : mask[k]? = some true)
    (hlen : k + 1 = mask.length) : kidx mask k + 1 = mask.count true := by
  rw [← kidx_length, ← hlen, kidx_succ hk]; rfl

/-! ## The deletion -/

variable {W : Type}

/-- **`vcK` is `vc` with the masked instructions deleted**, and no kept instruction or branch
argument reads a vreg in `G`. -/
structure Deletes (vc vcK : VCode) (mask : Nat → List Bool) (G : Nat → Prop) : Prop where
  blk : ∀ (b : Nat) (vb : VBlock), vc.blocks[b]? = some vb → ∃ vbK, vcK.blocks[b]? = some vbK ∧
    vbK.insts.toList = maskKeep (mask b) vb.insts.toList ∧ vbK.params = vb.params ∧
    vbK.branchArgs = vb.branchArgs
  len : ∀ (b : Nat) (vb : VBlock), vc.blocks[b]? = some vb → (mask b).length = vb.insts.size
  last : ∀ (b : Nat) (vb : VBlock), vc.blocks[b]? = some vb →
    vb.insts.size = 0 ∨ (mask b).getLast? = some true
  cfg : vcK.cfg = vc.cfg
  uses : ∀ (b : Nat) (vb : VBlock) (k : Nat) (i : MInst), vc.blocks[b]? = some vb →
    vb.insts[k]? = some i → (mask b)[k]? = some true →
    ∀ u ∈ vuseNums i, ¬ G u
  args : ∀ (b : Nat) (vb : VBlock) (r : Reg) (n : Nat), vc.blocks[b]? = some vb →
    r ∈ vb.branchArgs.toList → vregNum r = .ok n →
    ¬ G n

/-- **Corresponding configurations**: same block and world, the kept index of the position,
register files equal outside `G`; equal returns and halts. -/
def CorrC (mask : Nat → List Bool) (G : Nat → Prop) : VConf CV W → VConf CV W → Prop
  | .run vs, .run vsK => vsK.b = vs.b ∧ vsK.k = kidx (mask vs.b) vs.k ∧ vsK.w = vs.w ∧
      ∀ n, ¬ G n → vs.ρ n = vsK.ρ n
  | .ret v w, .ret v' w' => v' = v ∧ w' = w
  | .halt w, .halt w' => w' = w
  | _, _ => False

section
variable {vc vcK : VCode} {mask : Nat → List Bool} {G : Nat → Prop} {sem : ISem CV W}

theorem upd_congr_at {ρ ρ' : Nat → CV} {n a : Nat} {x : CV} (h : ρ n = ρ' n) :
    upd ρ a x n = upd ρ' a x n := by
  simp only [upd]; split <;> simp_all

theorem writeV_congr_at {n : Nat} : ∀ {dv : List (Operand × CV)} {ρ ρ' : Nat → CV},
    ρ n = ρ' n → writeV ρ dv n = writeV ρ' dv n
  | [], _, _, h => h
  | p :: dv, ρ, ρ', h => by
    simp only [writeV, List.foldl_cons] at *
    exact writeV_congr_at (dv := dv) (upd_congr_at h)

theorem vdefUpd_congr_at {ops : Array Operand} {outs : List CV} {ρ ρ' : Nat → CV} {n : Nat}
    (h : ρ n = ρ' n) : vdefUpd ops outs ρ n = vdefUpd ops outs ρ' n := by
  unfold vdefUpd
  exact writeV_congr_at (writeV_congr_at h)

theorem vuses_congr_of {i : MInst} {ops : Array Operand} (hops : i.operands = .ok ops)
    {ρ ρ' : Nat → CV} (h : ∀ u ∈ vuseNums i, ρ u = ρ' u) : vuses ops ρ = vuses ops ρ' := by
  unfold vuses
  apply List.map_congr_left
  intro o ho
  apply h
  simp only [vuseNums, hops, List.mem_map]
  exact ⟨o, ho, rfl⟩

theorem mem_of_lookup_some {l : List (Nat × Nat)} {a b : Nat} (h : l.lookup a = some b) :
    (a, b) ∈ l := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨p1, p2⟩ := p
    simp only [List.lookup_cons] at h
    split at h
    · rename_i he
      cases h
      have : a = p1 := by simpa using he
      subst this; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem parCopyEnv_congr_at {ρ ρ' : Nat → CV} {ps xs : List Nat} {n : Nat} (hn : ρ n = ρ' n)
    (hx : ∀ x ∈ xs, ρ x = ρ' x) : parCopyEnv ρ ps xs n = parCopyEnv ρ' ps xs n := by
  unfold parCopyEnv
  split
  · rename_i x hl
    exact hx x (List.of_mem_zip (mem_of_lookup_some hl)).2
  · exact hn

/-- `edgeEnv` is the parallel copy of the branch arguments' numbers into the parameters'. -/
theorem edgeEnv_spec {vc : VCode} {b s : Nat} {ρ ρ'' : Nat → CV}
    (h : edgeEnv vc b s ρ = some ρ'') :
    ∃ vb sb ps xs, vc.blocks[b]? = some vb ∧ vc.blocks[s]? = some sb ∧
      vb.branchArgs.size = sb.params.size ∧
      sb.params.toList.mapM vregNum = .ok ps ∧ vb.branchArgs.toList.mapM vregNum = .ok xs ∧
      ρ'' = parCopyEnv ρ ps xs := by
  unfold edgeEnv at h
  cases hvb : vc.blocks[b]? with
  | none => simp [hvb] at h
  | some vb =>
    cases hsb : vc.blocks[s]? with
    | none => simp [hvb, hsb] at h
    | some sb =>
      simp only [hvb, hsb, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · rename_i hsz
        cases hps : sb.params.toList.mapM vregNum with
        | error e => simp [hps, Except.toOption] at h
        | ok ps =>
          cases hxs : vb.branchArgs.toList.mapM vregNum with
          | error e => simp [hps, hxs, Except.toOption] at h
          | ok xs =>
            simp only [hps, hxs, Except.toOption, Option.bind_some, Option.pure_def,
              Option.some.injEq] at h
            exact ⟨vb, sb, ps, xs, rfl, rfl, hsz, hps, hxs, h.symm⟩
      · cases h

theorem edgeEnv_of_spec {vc : VCode} {b s : Nat} {vb sb : VBlock} {ps xs : List Nat}
    (hvb : vc.blocks[b]? = some vb) (hsb : vc.blocks[s]? = some sb)
    (hsz : vb.branchArgs.size = sb.params.size)
    (hps : sb.params.toList.mapM vregNum = .ok ps) (hxs : vb.branchArgs.toList.mapM vregNum = .ok xs)
    (ρ : Nat → CV) : edgeEnv vc b s ρ = some (parCopyEnv ρ ps xs) := by
  unfold edgeEnv
  simp [hvb, hsb, hsz, hps, hxs, Except.toOption]

theorem mem_of_mapM_vregNum : ∀ {rs : List Reg} {xs : List Nat}, rs.mapM vregNum = .ok xs →
    ∀ x ∈ xs, ∃ r ∈ rs, vregNum r = .ok x
  | [], xs, h => by simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; simp
  | r :: rs, xs, h => by
    rw [List.mapM_cons] at h
    cases hr : vregNum r with
    | error e => simp [hr, bind, Except.bind] at h
    | ok n =>
      cases hrs : rs.mapM vregNum with
      | error e => simp [hr, hrs, bind, Except.bind] at h
      | ok ns =>
        simp only [hr, hrs, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨r, List.mem_cons_self, hr⟩
        · obtain ⟨r', hr', h'⟩ := mem_of_mapM_vregNum hrs x hx
          exact ⟨r', List.mem_cons_of_mem _ hr', h'⟩

theorem succOf_congr {vc vc' : VCode} (h : vc'.cfg = vc.cfg) (b j : Nat) :
    succOf vc' b j = succOf vc b j := by
  simp only [succOf, h]

/-- **One kept step** of `vc` is a step of `vcK` from the corresponding configuration. -/
theorem vstep_deletes (hD : Deletes vc vcK mask G) {b k : Nat} {ρ : Nat → CV} {w : W}
    {c' : VConf CV W} (hs : VStep vc sem (.run ⟨b, k, ρ, w⟩) c')
    (hk : ∀ vb i, vc.blocks[b]? = some vb → vb.insts[k]? = some i → (mask b)[k]? = some true)
    {ρK : Nat → CV} (hρ : ∀ n, ¬ G n → ρ n = ρK n) :
    ∃ cK', VStep vcK sem (.run ⟨b, kidx (mask b) k, ρK, w⟩) cK' ∧ CorrC mask G c' cK' := by
  cases hs with
  | step hvb hi hops hsem hlen hn =>
    rename_i vb i ops outs w' ctl
    have hmk := hk vb i hvb hi
    obtain ⟨vbK, hvbK, hins, hpar, hba⟩ := hD.blk b vb hvb
    have hlenM := hD.len b vb hvb
    have hiK : vbK.insts[kidx (mask b) k]? = some i := by
      rw [← Array.getElem?_toList, hins,
        maskKeep_getElem? (by rw [hlenM]; simp) hmk, Array.getElem?_toList]
      exact hi
    have hsizeK : vbK.insts.size = (mask b).count true := by
      rw [← Array.length_toList, hins, length_maskKeep (by rw [hlenM]; simp)]
    have hu : ∀ u ∈ vuseNums i, ρ u = ρK u := fun u hu => hρ u (hD.uses b vb k i hvb hi hmk u hu)
    have hvu := vuses_congr_of hops hu
    have hagree : ∀ n, ¬ G n → vdefUpd ops outs ρ n = vdefUpd ops outs ρK n :=
      fun n hn => vdefUpd_congr_at (hρ n hn)
    have hsem' : sem i ((ops.toList.filter Operand.isUse).map (ρK ·.vreg)) w =
        some (outs, w', ctl) := by
      have : vuses ops ρK = vuses ops ρ := hvu.symm
      unfold vuses at this
      rw [this]; exact hsem
    have hlast : (mask b).getLast? = some true := by
      rcases hD.last b vb hvb with h0 | h
      · have := (Array.getElem?_eq_some_iff.mp hi).1; omega
      · exact h
    cases hn with
    | next hlt =>
      refine ⟨_, VStep.step hvbK hiK hops hsem' hlen (VNext.next ?_), ?_⟩
      · rw [hsizeK]; exact kidx_next_lt hmk hlast (by rw [hlenM]; exact hlt)
      · refine ⟨rfl, ?_, rfl, hagree⟩
        show kidx (mask b) k + 1 = kidx (mask b) (k + 1)
        rw [kidx_succ hmk]; rfl
    | goto hend hsucc henv =>
      rename_i j s ρ''
      obtain ⟨vb', sb, ps, xs, hvb', hsb, hsz, hps, hxs, rfl⟩ := edgeEnv_spec henv
      rw [hvb] at hvb'; cases hvb'
      obtain ⟨sbK, hsbK, -, hparS, -⟩ := hD.blk s sb hsb
      have henvK := edgeEnv_of_spec (vc := vcK) hvbK hsbK (by rw [hba, hparS]; exact hsz)
        (by rw [hparS]; exact hps) (by rw [hba]; exact hxs) (vdefUpd ops outs ρK)
      refine ⟨_, VStep.step hvbK hiK hops hsem' hlen (VNext.goto ?_ ?_ henvK), ?_⟩
      · rw [hsizeK]; exact kidx_last_eq hmk (by rw [hlenM]; exact hend)
      · rw [succOf_congr hD.cfg]; exact hsucc
      · refine ⟨rfl, by simp, rfl, fun n hn => parCopyEnv_congr_at (hagree n hn) ?_⟩
        intro x hx
        obtain ⟨r, hr, hrx⟩ := mem_of_mapM_vregNum hxs x hx
        exact hagree x (hD.args b vb r x hvb hr hrx)
    | ret hi' =>
      refine ⟨_, VStep.step hvbK hiK hops hsem' hlen (VNext.ret hi'), ?_⟩
      exact ⟨by unfold vuses at hvu; exact hvu.symm, rfl⟩
    | halt =>
      exact ⟨_, VStep.step hvbK hiK hops hsem' hlen VNext.halt, rfl⟩

/-- **Kept runs move to the deleted VCode**: a run of `vc` executing only from configurations
satisfying `P`, where `P` implies the position is kept, is a run of `vcK` between corresponding
configurations. -/
theorem starP_deletes (hD : Deletes vc vcK mask G) {P : VConf CV W → Prop}
    (hP : ∀ b k ρ w, P (.run ⟨b, k, ρ, w⟩) → ∀ vb i, vc.blocks[b]? = some vb →
      vb.insts[k]? = some i → (mask b)[k]? = some true) :
    ∀ {c c' : VConf CV W}, StarP (VStep vc sem) P c c' → ∀ cK, CorrC mask G c cK →
      ∃ cK', Star (VStep vcK sem) cK cK' ∧ CorrC mask G c' cK'
  | _, _, .refl _, cK, h => ⟨cK, .refl _, h⟩
  | _, _, .step hp hs t, cK, h => by
    rename_i c c₁ c'
    cases c with
    | run vs =>
      obtain ⟨b, k, ρ, w⟩ := vs
      cases cK with
      | run vsK =>
        obtain ⟨bK, kK, ρK, wK⟩ := vsK
        obtain ⟨hb, hkk, hw, hρ⟩ := h
        simp only at hb hkk hw hρ
        subst bK kK wK
        obtain ⟨cK₁, hsK, hC₁⟩ := vstep_deletes hD hs (hP b k ρ w hp) hρ
        obtain ⟨cK', hstar, hC'⟩ := starP_deletes hD hP t cK₁ hC₁
        exact ⟨cK', .step hsK hstar, hC'⟩
      | ret v w => exact absurd h id
      | halt w => exact absurd h id
    | ret _ _ => cases hs
    | halt _ => cases hs

theorem VTrapFromP.deletes (hD : Deletes vc vcK mask G) {P : VConf CV W → Prop}
    (hP : ∀ b k ρ w, P (.run ⟨b, k, ρ, w⟩) → ∀ vb i, vc.blocks[b]? = some vb →
      vb.insts[k]? = some i → (mask b)[k]? = some true)
    {vs vsK : VState CV W} {c : Clif.TrapCode} (h : VTrapFromP P vc sem vs c)
    (hC : CorrC mask G (.run vs) (.run vsK)) : VTrapFrom vcK sem vsK c := by
  obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hs, hp, hvb, hi, hops, hsem, htc⟩ := h
  obtain ⟨cK, hsK, hCK⟩ := starP_deletes hD hP hs _ hC
  cases cK with
  | run vsK' =>
    obtain ⟨b', k', ρK, wK⟩ := vsK'
    obtain ⟨hb, hk, hw, hρ⟩ := hCK
    simp only at hb hk hw hρ
    subst b' k' wK
    have hmk := hP b k ρ w hp vb i hvb hi
    obtain ⟨vbK, hvbK, hins, -, -⟩ := hD.blk b vb hvb
    have hiK : vbK.insts[kidx (mask b) k]? = some i := by
      rw [← Array.getElem?_toList, hins,
        maskKeep_getElem? (by rw [hD.len b vb hvb]; simp) hmk, Array.getElem?_toList]
      exact hi
    have hvu := vuses_congr_of hops (fun u hu => hρ u (hD.uses b vb k i hvb hi hmk u hu))
    exact ⟨b, _, ρK, w, vbK, i, ops, outs, w', hsK, hvbK, hiK, hops, by rw [← hvu]; exact hsem, htc⟩
  | ret _ _ => exact absurd hCK id
  | halt _ => exact absurd hCK id

theorem VRetFromP.deletes (hD : Deletes vc vcK mask G) {P : VConf CV W → Prop}
    (hP : ∀ b k ρ w, P (.run ⟨b, k, ρ, w⟩) → ∀ vb i, vc.blocks[b]? = some vb →
      vb.insts[k]? = some i → (mask b)[k]? = some true)
    {vs vsK : VState CV W} {us : List (Reg × Reg)} {vals : List CV} {w' : W}
    (h : VRetFromP P vc sem vs us vals w')
    (hC : CorrC mask G (.run vs) (.run vsK)) : VRetFrom vcK sem vsK us vals w' := by
  obtain ⟨b, k, ρ, w, vb, ops, outs, hs, hp, hvb, hi, hops, hvals, hsem⟩ := h
  obtain ⟨cK, hsK, hCK⟩ := starP_deletes hD hP hs _ hC
  cases cK with
  | run vsK' =>
    obtain ⟨b', k', ρK, wK⟩ := vsK'
    obtain ⟨hb, hk, hw, hρ⟩ := hCK
    simp only at hb hk hw hρ
    subst b' k' wK
    have hmk := hP b k ρ w hp vb _ hvb hi
    obtain ⟨vbK, hvbK, hins, -, -⟩ := hD.blk b vb hvb
    have hiK : vbK.insts[kidx (mask b) k]? = some (.rets us) := by
      rw [← Array.getElem?_toList, hins,
        maskKeep_getElem? (by rw [hD.len b vb hvb]; simp) hmk, Array.getElem?_toList]
      exact hi
    have hvu := vuses_congr_of hops (fun u hu => hρ u (hD.uses b vb k _ hvb hi hmk u hu))
    exact ⟨b, _, ρK, w, vbK, ops, outs, hsK, hvbK, hiK, hops, by rw [hvals, hvu], hsem⟩
  | ret _ _ => exact absurd hCK id
  | halt _ => exact absurd hCK id

end

end Backend.Proof.Driver
