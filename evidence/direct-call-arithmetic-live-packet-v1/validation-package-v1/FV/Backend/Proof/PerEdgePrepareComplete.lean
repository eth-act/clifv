import FV.Backend.Proof.PerEdgePrepareOrderFacts
import FV.Backend.Proof.PerEdgePrepareFacts
import FV.Backend.RegallocPerEdgePrepareCheck

namespace Backend.Proof.PerEdgePrep
open Backend Backend.Proof Backend.Proof.Driver

private theorem kept_row {vc : VCode} {edges : Array EdgeRow} {ss : Array (Array Nat)}
    (count : edges.size = vc.blocks.size) (labels : Prep.Lbls vc.blocks)
    {k b : Nat} (hk : k < (Prep.keep vc.blocks (reachable ss)).size) (hb : b < vc.blocks.size)
    (block : (Prep.keep vc.blocks (reachable ss))[k] = vc.blocks[b]) :
    ((keptAt vc edges ss).map Prod.snd)[k]! = edges[b]! := by
  have proj := keptAt_blocks (ss := ss) count
  have hkp : k < (keptAt vc edges ss).size := by rw [← proj,Array.size_map] at hk; exact hk
  obtain ⟨b',source,row,_⟩ := keptAt_source hkp
  obtain ⟨hb',same⟩ := Array.getElem?_eq_some_iff.mp source
  have pairBlock : (keptAt vc edges ss)[k].1 = vc.blocks[b] := by
    have eq := congrArg (fun a : Array VBlock => a[k]?) proj
    simp only [Array.getElem?_map,Array.getElem?_eq_getElem hkp,
      Array.getElem?_eq_getElem hk,Option.map_some,Option.some.injEq] at eq
    exact eq.trans block
  have idx : b' = b := Prep.lbl_inj labels hb' hb (congrArg VBlock.label (same.trans pairBlock))
  subst b'
  rw [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?]
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem hkp,Option.map_some,Option.getD_some]
  rw [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,row]
  rfl

private theorem block_copy_route {E : Array VBlock} {rows : Array EdgeRow}
    {vb vb' : VBlock} {original row : EdgeRow} (copies : BlockCopies E rows vb vb' original row)
    {t t' : MInst} (old : vb.insts.back? = some t) (new : vb'.insts.back? = some t')
    {j : Nat} {target : Label} {args : Array Reg}
    (htarget : t.targets[j]? = some target) (hargs : original[j]? = some args) :
    ∃ label, t'.targets[j]? = some label ∧
      ((label = target ∧ row[j]? = some args) ∨
        (row[j]? = some #[] ∧ ∃ e : Nat,
          E[e]? = some {label := label,insts := #[.jump target],branchArgs := args} ∧
          rows[e]? = some #[args])) := by
  rcases copies with ⟨rfl,rfl⟩ | ⟨t0,t0',ls,back,retarget,rfl,routes⟩
  · rw [old] at new
    cases new
    exact ⟨target,htarget,.inl ⟨rfl,hargs⟩⟩
  · rw [old] at back
    cases back
    simp only [Array.back?_push,Option.some.injEq] at new
    subst t'
    obtain ⟨label,atLabel,route⟩ := routes j target args htarget hargs
    refine ⟨label,?_,route⟩
    rw [(Prep.setTargets_targets retarget).1,Array.getElem?_toList]
    exact atLabel

private theorem mapped_row {order : Array Nat} {rows : Array EdgeRow} {q k : Nat}
    (atIndex : order[q]? = some k) :
    (order.map fun i => rows[i]!)[q]? = some rows[k]! := by
  simp only [Array.getElem?_map,atIndex,Option.map_some]

/-- Every live source block is accepted by the actual indexed preparation
relation after the real filtering, splitting and RPO stages. -/
theorem live_okAt {vc : VCode} {edges : Array EdgeRow} {p : EdgeVCode}
    (run : prepareAt vc edges = .ok p) (nonempty : 0 < vc.blocks.size)
    (labels : Prep.Lbls vc.blocks) {ss0 ps0 ss3 ps3 : Array (Array Nat)}
    (cfg0 : vc.cfg = .ok (ss0,ps0)) (cfg3 : p.code.cfg = .ok (ss3,ps3))
    {b : Nat} (hb : b < vc.blocks.size) (live : Prep.mk (reachable ss0) b) :
    ∃ q, sigmaOf vc p.code b = some q ∧ keptOkAt vc p.code edges p.edges ss0 ss3 b q = true := by
  obtain ⟨count,ssA,psA,ss1,ps1,ss2,ps2,st,cfgA,dimensions,cfg1,inv,cfg2,result⟩ :=
    prepareAt_kept_facts run
  rw [cfg0] at cfgA
  cases cfgA
  have cs0 := Prep.cfg_spec cfg0
  have cs1 := Prep.cfg_spec cfg1
  have cs2 := Prep.cfg_spec cfg2
  have cs3 := Prep.cfg_spec cfg3
  have nonzero : ss0.size ≠ 0 := by rw [cs0.size]; omega
  have entry := (Prep.reachable_spec (Prep.succsIn_of cs0) nonzero).2.1
  obtain ⟨keptNonempty,_⟩ := Prep.keep_zero nonempty entry
  obtain ⟨lbls,bounds,nodup,_,_,_,reach⟩ := outer_order_facts inv cs1 cs2
    (Prep.keep_lbls labels (reachable ss0)) keptNonempty
  have sourceReach := (Prep.reachable_spec (Prep.succsIn_of cs0) nonzero).2.2.2 b live
  obtain ⟨k,hk,_,original,keptReach⟩ := Prep.reach01 cs0 cs1 labels nonempty sourceReach
  obtain ⟨q,hq,orderK,find⟩ := Prep.lab3 bounds lbls nodup (reach k keptReach).2
  have hkB : k < st.2.1.size := by rw [inv.graph.size]; exact hk
  have hk2 : k < (st.2.1 ++ st.2.2.2.1).size := by simp; omega
  have atB : (st.2.1 ++ st.2.2.2.1)[k] = st.2.1[k] := Array.getElem_append_left hkB
  obtain ⟨_,t,t',back,back',label,params,args,size,pop,last,len,_⟩ := Prep.blk2 inv.graph cs1 hk
  rw [original] at back label params args size pop
  have oldRow := kept_row count labels hk hb original
  have copies := inv.copies k hk hkB
  rw [original,oldRow] at copies
  have orderedBlock : ((rpo ss2).map fun i => (st.2.1 ++ st.2.2.2.1)[i]!)[q]? = some st.2.1[k] := by
    obtain ⟨_,lookup⟩ := Prep.v3_get bounds hq
    rw [lookup]
    congr 1
    simpa only [orderK] using atB
  have orderK' : (rpo ss2)[q]? = some k := by
    rw [Array.getElem?_eq_getElem hq,orderK]
  have sourceRow : ∃ row, edges[b]? = some row := by
    have he : b < edges.size := by rw [count]; exact hb
    exact ⟨_,Array.getElem?_eq_getElem he⟩
  obtain ⟨row,rowAt⟩ := sourceRow
  have rowSize := dimensions b row rowAt
  have rowVal : edges[b]! = row := by rw [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,rowAt]; rfl
  have keptRowBound : k < st.2.2.1.size := by rw [inv.rowCount]; exact hkB
  have preparedRow : ((rpo ss2).map fun i => (st.2.2.1 ++ st.2.2.2.2)[i]!)[q]? =
      some st.2.2.1[k]! := by
    rw [mapped_row orderK']
    congr 1
    rw [getElem!_pos (st.2.2.1 ++ st.2.2.2.2) k (by simp; omega),
      Array.getElem_append_left keptRowBound,getElem!_pos st.2.2.1 k keptRowBound]
  have hσ : ∀ s (hs : s < vc.blocks.size), sigmaOf vc p.code s =
      Prep.lab p.code.blocks vc.blocks[s].label := fun s hs => by
    unfold sigmaOf
    rw [Array.getElem?_eq_getElem hs]
    rfl
  have pBlocks : p.code.blocks = (rpo ss2).map fun i => (st.2.1 ++ st.2.2.2.1)[i]! := by rw [result]
  have pRows : p.edges = (rpo ss2).map fun i => (st.2.2.1 ++ st.2.2.2.2)[i]! := by rw [result]
  have blockAt : p.code.blocks[q]? = some st.2.1[k] := by rw [pBlocks]; exact orderedBlock
  have rowAt' : p.edges[q]? = some st.2.2.1[k]! := by rw [pRows]; exact preparedRow
  have labelAt : (st.2.1 ++ st.2.2.2.1)[k]!.label = vc.blocks[b].label := by
    rw [getElem!_pos _ k hk2,atB,label]
  rw [labelAt] at find
  refine ⟨q,by rw [hσ b hb,pBlocks]; exact find,?_⟩
  unfold keptOkAt
  rw [Array.getElem?_eq_getElem hb,blockAt]
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨params,args⟩,size⟩,pop⟩,?_⟩,?_⟩
  · unfold lastOk
    rw [back,back']
    simp only [Bool.or_eq_true,decide_eq_true_eq]
    exact last
  · obtain ⟨t0,sb,back0,_,sbAt,sbSize,targets0⟩ := cs0.blk b _ (Array.getElem?_eq_getElem hb)
    rw [back] at back0
    cases back0
    obtain ⟨t3,sb',back3,_,sbAt',sbSize',targets3⟩ := cs3.blk q _ blockAt
    rw [back'] at back3
    cases back3
    rw [sbAt,sbAt']
    simp only [Bool.and_eq_true,decide_eq_true_eq]
    refine ⟨by rw [sbSize',len,sbSize],?_⟩
    rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    have hjRow : j < row.size := by
      have sbVal : ss0[b]! = sb := by rw [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,sbAt]; rfl
      rw [rowSize,sbVal]
      exact hj
    let outgoing := row[j]
    have vector : edges[b]![j]? = some outgoing := by rw [rowVal]; exact Array.getElem?_eq_getElem hjRow
    obtain ⟨l,hl⟩ : ∃ l, t.targets[j]? = some l :=
      ⟨_,List.getElem?_eq_getElem (by rw [← sbSize]; exact hj)⟩
    obtain ⟨l',hl',route⟩ := block_copy_route copies back back' hl vector
    obtain ⟨s,hs,findS⟩ := targets0 j l hl
    obtain ⟨u,hu,findU⟩ := targets3 j l' hl'
    rw [hs,hu]
    simp only
    obtain ⟨hsBound,sLabel⟩ := Prep.lab_some findS
    rw [hσ s hsBound,sLabel,pBlocks]
    have sourceVector : (edges[b]?.bind (·[j]?)) = some outgoing := by
      rw [rowAt]
      exact Array.getElem?_eq_getElem hjRow
    rcases route with ⟨same,copy⟩ | ⟨empty,e,edge,edgeRow⟩
    · rw [same] at findU
      rw [← pBlocks,findU]
      simp only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
      exact .inl ⟨trivial,by rw [rowAt',sourceVector]; exact copy⟩
    · obtain ⟨huR,hiu,lookupU,labelU⟩ := Prep.lab3_inv bounds (by rw [← pBlocks]; exact findU)
      have he : e < st.2.2.2.1.size := (Array.getElem?_eq_some_iff.mp edge).1
      have syntheticAt : (st.2.1 ++ st.2.2.2.1)[st.2.1.size + e]? =
          some {label := l',insts := #[.jump l],branchArgs := outgoing} := by
        rw [Array.getElem?_append_right (by omega)]
        simpa using edge
      have syntheticBound := (Array.getElem?_eq_some_iff.mp syntheticAt).1
      have syntheticEq := (Array.getElem?_eq_some_iff.mp syntheticAt).2
      have indexU : (rpo ss2)[u] = st.2.1.size + e :=
        Prep.lbl_inj lbls hiu syntheticBound (by rw [labelU,syntheticEq])
      have blockU : p.code.blocks[u]? =
          some {label := l',insts := #[.jump l],branchArgs := outgoing} := by
        rw [pBlocks,lookupU]
        congr 1
        simpa only [indexU] using syntheticEq
      have rowU : p.edges[u]? = some #[outgoing] := by
        rw [pRows,mapped_row (Array.getElem?_eq_getElem huR)]
        rw [indexU]
        have rowIndex : st.2.1.size + e = st.2.2.1.size + e := by rw [inv.rowCount]
        rw [rowIndex,Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,
          Array.getElem?_append_right (by omega)]
        simp only [Nat.add_sub_cancel_left,edgeRow,Option.getD_some]
      obtain ⟨jump,successors,atJump,_,atSuccs,countSuccs,targetJump⟩ := cs3.blk u _ blockU
      simp only [Array.back?] at atJump
      simp at atJump
      subst jump
      obtain ⟨w,hw,findW⟩ := targetJump 0 l rfl
      have singleton : successors = #[w] := by
        apply Array.ext
        · simp [countSuccs,MInst.targets]
        · intro i hi _
          have zero : i = 0 := by simp [countSuccs,MInst.targets] at hi; omega
          subst i
          simp only [Array.getElem?_eq_getElem hi,Option.some.injEq] at hw
          simpa using hw
      rw [← pBlocks,findW]
      simp only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
      refine .inr ⟨⟨?_,?_⟩,?_⟩
      · rw [rowAt']
        exact empty
      · unfold edgeBlockOkAt
        rw [blockU]
        simp [atSuccs,singleton]
      · rw [rowU,sourceVector]
        rfl

private theorem inst_origin {vc : VCode} {edges : Array EdgeRow} {p : EdgeVCode}
    (run : prepareAt vc edges = .ok p) (nonempty : 0 < vc.blocks.size)
    (labels : Prep.Lbls vc.blocks) {vb' : VBlock} (block : vb' ∈ p.code.blocks.toList)
    {i' : MInst} (inst : i' ∈ vb'.insts.toList) :
    (∃ vb ∈ vc.blocks.toList, i' ∈ vb.insts.toList) ∨
      (∃ vb ∈ vc.blocks.toList, ∃ i ∈ vb.insts.toList, ∃ ls, i.setTargets ls = some i') ∨
      ∃ l, i' = .jump l := by
  obtain ⟨_,ss0,ps0,ss1,ps1,ss2,ps2,st,cfg0,_,cfg1,inv,cfg2,result⟩ := prepareAt_kept_facts run
  have cs0 := Prep.cfg_spec cfg0
  have nonzero : ss0.size ≠ 0 := by rw [cs0.size]; omega
  obtain ⟨keptNonempty,_⟩ := Prep.keep_zero nonempty
    (Prep.reachable_spec (Prep.succsIn_of cs0) nonzero).2.1
  obtain ⟨_,bounds,_⟩ := outer_order_facts inv (Prep.cfg_spec cfg1) (Prep.cfg_spec cfg2)
    (Prep.keep_lbls labels (reachable ss0)) keptNonempty
  rw [result] at block
  rw [Array.mem_toList_iff,Array.mem_map] at block
  obtain ⟨k,hk,rfl⟩ := block
  have bound : k < (st.2.1 ++ st.2.2.2.1).size := bounds k (by simpa using hk)
  rw [getElem!_pos _ k bound] at inst
  by_cases old : k < st.2.1.size
  · rw [Array.getElem_append_left old] at inst
    have hkV : k < (Prep.keep vc.blocks (reachable ss0)).size := by rw [← inv.graph.size]; exact old
    obtain ⟨b,hb,source,_⟩ := Prep.keep_src hkV
    have member : (Prep.keep vc.blocks (reachable ss0))[k] ∈ vc.blocks.toList := by rw [source]; simp
    rcases inv.graph.rw k hkV old with same | ⟨t,t',ls,back,_,retarget,rewrite,_⟩
    · rw [same] at inst
      exact .inl ⟨_,member,inst⟩
    · rw [rewrite] at inst
      simp only [Array.toList_push,List.mem_append,List.mem_singleton] at inst
      rcases inst with inst | rfl
      · exact .inl ⟨_,member,Prep.pop_mem inst⟩
      · exact .inr (.inl ⟨_,member,t,Array.mem_toList_iff.mpr (Array.mem_of_back? back),ls,retarget⟩)
  · rw [Array.getElem_append_right (Nat.le_of_not_lt old)] at inst
    have he : k - st.2.1.size < st.2.2.2.1.size := by simp at bound; omega
    obtain ⟨l,shape⟩ := inv.graph.edges (k - st.2.1.size) (by simpa using he)
    have insts : st.2.2.2.1[k - st.2.1.size].insts = #[.jump l] := by
      have h := congrArg VBlock.insts shape
      simpa only [Array.getElem_map,graphBlock] using h
    rw [insts] at inst
    simp at inst
    exact .inr (.inr ⟨l,inst⟩)

private theorem any_from_output {vc : VCode} {edges : Array EdgeRow} {p : EdgeVCode}
    (run : prepareAt vc edges = .ok p) (nonempty : 0 < vc.blocks.size)
    (labels : Prep.Lbls vc.blocks) (P : MInst → Bool)
    (retarget : ∀ i ls i', i.setTargets ls = some i' → P i' = true → P i = true)
    (jump : ∀ l, P (.jump l) = false)
    (h : (p.code.blocks.any fun b => b.insts.any P) = true) :
    (vc.blocks.any fun b => b.insts.any P) = true := by
  rw [Array.any_eq_true'] at h ⊢
  obtain ⟨b,member,hasInst⟩ := h
  rw [Array.any_eq_true'] at hasInst
  obtain ⟨i,inst,property⟩ := hasInst
  rcases inst_origin run nonempty labels (Array.mem_toList_iff.mpr member)
      (Array.mem_toList_iff.mpr inst) with
    ⟨vb,hvb,hi⟩ | ⟨vb,hvb,old,hold,ls,hset⟩ | ⟨l,rfl⟩
  · exact ⟨vb,Array.mem_toList_iff.mp hvb,Array.any_eq_true'.mpr ⟨i,Array.mem_toList_iff.mp hi,property⟩⟩
  · exact ⟨vb,Array.mem_toList_iff.mp hvb,
      Array.any_eq_true'.mpr ⟨old,Array.mem_toList_iff.mp hold,retarget old ls i hset property⟩⟩
  · rw [jump] at property
    cases property

/-- Preparation introduces neither TryCall nor TLS effects, including when
retargeting their real instruction forms; copied vectors impose no restriction. -/
theorem prepareAt_no_new_effects {vc : VCode} {edges : Array EdgeRow} {p : EdgeVCode}
    (run : prepareAt vc edges = .ok p) (nonempty : 0 < vc.blocks.size)
    (labels : Prep.Lbls vc.blocks) :
    (vc.hasTryCall || !p.code.hasTryCall) = true ∧ (vc.hasTls || !p.code.hasTls) = true := by
  constructor
  · simp only [Bool.or_eq_true,Bool.not_eq_true']
    by_cases h : vc.hasTryCall = true
    · exact .inl h
    · right
      cases hp : p.code.hasTryCall with
      | false => rfl
      | true =>
        refine absurd (any_from_output run nonempty labels (fun i => i matches .tryCall ..) ?_ ?_ hp) h
        · intro i ls i' hset hi
          obtain ⟨_,_,source,_⟩ := Prep.setTargets_targets hset
          obtain ⟨a,b,rfl⟩ := source (by cases i' <;> simp_all)
          rfl
        · intro l
          rfl
  · simp only [Bool.or_eq_true,Bool.not_eq_true']
    by_cases h : vc.hasTls = true
    · exact .inl h
    · right
      cases hp : p.code.hasTls with
      | false => rfl
      | true =>
        refine absurd (any_from_output run nonempty labels (fun i => i matches .elfTlsGetAddr ..) ?_ ?_ hp) h
        · intro i ls i' hset hi
          obtain ⟨_,_,_,noTls⟩ := Prep.setTargets_targets hset
          cases i' <;> simp_all
        · intro l
          rfl

/-- Completeness of the actual per-successor preparation relation. The only
graph-domain conditions are nonemptiness and distinct labels; no legacy common
outgoing vector or empty multi-successor argument restriction is required. -/
theorem prepCheckAt_complete {vc : VCode} {edges : Array EdgeRow} {p : EdgeVCode}
    (run : prepareAt vc edges = .ok p) (nonempty : 0 < vc.blocks.size)
    (labels : Prep.Lbls vc.blocks) : prepCheckAt vc edges p = true := by
  obtain ⟨ss0,ps0,ss1,ps1,ss2,ps2,st,cfg0,cfg1,loop,cfg2,result⟩ := prepareAt_stages run
  obtain ⟨_,ss3,ps3,cfg3⟩ := prepareAt_cfg run nonempty labels
  have cs0 := Prep.cfg_spec cfg0
  have nonzero : ss0.size ≠ 0 := by rw [cs0.size]; omega
  obtain ⟨_,entry,closed,_⟩ := Prep.reachable_spec (Prep.succsIn_of cs0) nonzero
  have effects := prepareAt_no_new_effects run nonempty labels
  have metadata := prepareAt_fields run
  unfold prepCheckAt
  dsimp only
  rw [cfg0,cfg3]
  simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
  refine ⟨⟨⟨prepareAt_entry run nonempty labels,entry⟩,?_⟩,⟨effects.1,effects.2⟩,metadata.2.2.2.1⟩
  rw [List.all_eq_true]
  intro b hb
  rw [List.mem_range] at hb
  simp only [Bool.or_eq_true,Bool.not_eq_true']
  by_cases live : Prep.mk (reachable ss0) b
  · right
    obtain ⟨q,atQ,accepted⟩ := live_okAt run nonempty labels cfg0 cfg3 hb live
    rw [atQ]
    simp only [Bool.and_eq_true]
    refine ⟨accepted,?_⟩
    have row : ss0[b]?.getD #[] = ss0[b]! := by
      simp only [getElem!_def]
      split <;> simp_all <;> rfl
    rw [row,Array.all_eq_true]
    intro j hj
    have successor : ss0[b]![j] ∈ ss0[b]!.toList := Array.getElem_mem_toList hj
    simp only [Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨cs0.size ▸ Prep.succsIn_of cs0 b _ successor,closed b live _ successor⟩
  · left
    simpa [liveOf,Prep.mk] using live

/-- On the same original graph domain, the internal check cannot reject an
actual successful indexed preparation. No checker verdict is a caller premise. -/
theorem prepareCheckedAt_complete {vc : VCode} {edges : Array EdgeRow} {p : EdgeVCode}
    (run : prepareAt vc edges = .ok p) (nonempty : 0 < vc.blocks.size)
    (labels : Prep.Lbls vc.blocks) : prepareCheckedAt vc edges = .ok p := by
  simp [prepareCheckedAt,run,bind,Except.bind,pure,Except.pure,
    prepCheckAt_complete run nonempty labels]

end Backend.Proof.PerEdgePrep
