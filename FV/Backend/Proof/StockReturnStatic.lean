import FV.Backend.Proof.StockReturnRecordCalls
import FV.Backend.Proof.StockTerminalEmission
import FV.Backend.Proof.IselShpCtor
import FV.Backend.Proof.StockWholeClasses
namespace Backend.Stock.Proof.ReturnStaticDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem return_alloc9 : ∀ k ≤ 8,(Reg.x k).allocatable = true ∧ Reg.x k ∉ calleeSaved := by decide
private theorem rets_fixed9 {ns : List (Nat × Reg)} (hr : ∀ q ∈ ns, ∃ k, k ≤ 8 ∧ q.2 = .x k)
    (hnd : (ns.map (·.2)).Nodup) : SpillInstOk (.rets (retPairs ns)) := by
  have mem : ∀ o ∈ (retOps ns).toArray.toList, ∃ q ∈ ns, o = ⟨q.1, .int, .use, .early, .fixed q.2⟩ := by
    intro o ho
    simp only [retOps, List.mem_map] at ho
    obtain ⟨q, hq, rfl⟩ := ho
    exact ⟨q, hq, rfl⟩
  have memj : ∀ (j : Nat) (o : Operand), (retOps ns).toArray.toList[j]? = some o → ∃ q ∈ ns,
      o = ⟨q.1, .int, .use, .early, .fixed q.2⟩ := fun j o hj => mem o (List.mem_of_getElem? hj)
  have nodef : ∀ o ∈ (retOps ns).toArray.toList, o.kind = .use := by
    intro o ho; obtain ⟨q, -, rfl⟩ := mem o ho; rfl
  refine ⟨_, operands_rets ns, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro o ho h; obtain ⟨q, -, rfl⟩ := mem o ho; cases h
  · intro o ho _; obtain ⟨q, -, rfl⟩ := mem o ho; rfl
  · intro o ho p h; obtain ⟨q, hq, rfl⟩ := mem o ho
    cases h
    obtain ⟨k, hk, he⟩ := hr q hq
    rw [he]; exact ⟨(return_alloc9 k hk).1, rfl⟩
  · intro o ho o' ho' p _ _ h h'
    obtain ⟨q, hq, rfl⟩ := mem o ho
    obtain ⟨q', hq', rfl⟩ := mem o' ho'
    injection h with h; injection h' with h'
    rw [inj_of_nodup_map hnd hq hq' (h.trans h'.symm)]
  · intro j j' o o' p hj _ hd
    obtain ⟨q, -, rfl⟩ := memj j o hj; cases hd
  · intro o ho p hd; rw [nodef o ho] at hd; cases hd
  · intro o ho hd; rw [nodef o ho] at hd; cases hd
  · intro j o i hj h; obtain ⟨q, -, rfl⟩ := memj j o hj; cases h
  · intro c
    have : nScratch c (retOps ns).toArray.toList = 0 := by
      unfold nScratch
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro o ho; obtain ⟨q, -, rfl⟩ := mem o ho; simp [scratch]
    omega
  · have : (retOps ns).toArray.toList.filter (·.kind == .def) = [] := by
      rw [List.filter_eq_nil_iff]; intro o ho; simp [nodef o ho]
    rw [this]; exact List.nodup_nil
  · intro us _ o ho
    obtain ⟨q, hq, rfl⟩ := mem o ho
    obtain ⟨k, hk, he⟩ := hr q hq
    exact ⟨q.2, rfl, he ▸ (return_alloc9 k hk).2⟩

private theorem pins_nine {f : Clif.Function} {count : Nat} {ps : List Reg}
    (pins : returnPins f count = some ps) :
    (∀ r ∈ ps,∃ k,k ≤ 8 ∧ r = .x k) ∧ ps.Nodup := by
  unfold returnPins at pins
  split at pins
  · cases pins
    exact ⟨by intro r member; have equal := List.mem_singleton.mp member; subst r; exact ⟨8,by decide,rfl⟩,by simp⟩
  · obtain ⟨bound,rfl⟩ := retRegs_eq pins
    refine ⟨?_,?_⟩
    · intro r member
      obtain ⟨n,below,rfl⟩ := List.mem_map.mp member
      exact ⟨n,by simp only [List.mem_range] at below; omega,rfl⟩
    · exact List.Pairwise.map Reg.x (fun _ _ different same => different (by cases same; rfl)) List.nodup_range

private theorem pinned_static {f : Clif.Function} {rs ps : List Reg}
    (mapped : ∀ r ∈ rs,∃ n,r = .vreg n .int) (pins : returnPins f rs.length = some ps) :
    SpillInstOk (.rets (rs.zip ps)) := by
  obtain ⟨shape,distinct⟩ := pins_nine pins
  obtain ⟨ns,equal,subset⟩ := zip_retPairs rs ps mapped
  rw [← equal]
  exact rets_fixed9 (fun q member => shape q.2 (subset.subset (List.mem_map_of_mem member))) (subset.nodup distinct)

private theorem option_map_length {α β : Type} (g : α → Option β) :
    ∀ (xs : List α) (ys : List β),xs.mapM g = some ys → ys.length = xs.length
  | [],ys,run => by cases run; rfl
  | x :: xs,ys,run => by
    rw [List.mapM_cons] at run
    cases head : g x with
    | none => simp only [head,bind,Option.bind] at run; cases run
    | some y =>
      cases tail : xs.mapM g with
      | none => simp only [head,tail,bind,Option.bind] at run; cases run
      | some rest =>
        simp only [head,tail,bind,Option.bind,pure] at run
        cases run
        simpa only [List.length_cons] using congrArg Nat.succ (option_map_length g xs rest tail)

private theorem unpack_members {rss : List (List Reg)} {rs : List Reg}
    (run : unpackReturnRegs rss = some rs) :
    rs.length = rss.length ∧ ∀ r ∈ rs,∃ xs ∈ rss,r ∈ xs := by
  unfold unpackReturnRegs at run
  refine ⟨option_map_length _ _ _ run,?_⟩
  intro r member
  obtain ⟨xs,present,one⟩ := mapM_mem run r member
  cases xs with
  | nil => cases one
  | cons x rest =>
    cases rest with
    | cons y more => cases one
    | nil => cases one; exact ⟨[r],present,by simp⟩

/-- Actual revised gen_return derives pin selection and static operand validity,
including implicit x8, without projecting to the legacy x0..x7 constructor. -/
theorem stock_gen_return_static {ctx : Ctx} {rss : List (List Reg)} {before after : State} {value : V}
    (virtual : ∀ xs ∈ rss,∀ r ∈ xs,∃ n,r = .vreg n .int)
    (run : Stock.externCtor ctx T.gen_return [.regsVec rss] before = .ok (value,after)) :
    ∃ rs ps,returnPins ctx.func rs.length = some ps ∧ unpackReturnRegs rss = some rs ∧
      after = {before with base := before.base.emit (.rets (rs.zip ps))} ∧ value = .op .unit ∧
      SpillInstOk (.rets (rs.zip ps)) := by
  obtain ⟨rs,ps,pins,unpacked,state,unit⟩ := stock_gen_return_shape run
  have members := unpack_members unpacked
  have pinned : returnPins ctx.func rs.length = some ps := by rw [members.1]; exact pins
  refine ⟨rs,ps,pinned,unpacked,state,unit,pinned_static ?_ pinned⟩
  intro r member
  obtain ⟨xs,present,held⟩ := members.2 r member
  exact virtual xs present r held

private theorem pinned_resolved_static {f : Clif.Function} {rs ps : List Reg}
    (mapped : ∀ r ∈ rs,∃ n,r = .vreg n .int) (pins : returnPins f rs.length = some ps)
    (aliases : Array (Option Nat)) :
    SpillInstOk ((.rets (rs.zip ps) : MInst).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1))) := by
  obtain ⟨gn,aliasRenaming⟩ := resolve_vrenaming aliases (aliases.size+1)
  apply spillInstOk_mapRegs aliasRenaming (pinned_static mapped pins)
  intro ops operands o member defined
  obtain ⟨ns,equal,subset⟩ := zip_retPairs rs ps mapped
  rw [← equal,operands_rets ns] at operands
  cases operands
  simp only [List.toList_toArray,retOps,List.mem_map] at member
  obtain ⟨q,present,rfl⟩ := member
  cases defined

/-- The actual retained original return derives its complete static operand
validity, including x8 struct returns, through the real selected helper and
empty binder. Final alias renaming preserves it without a def-fixing premise.
No caller step/decision, pin, helper or operand-validity certificate is used. -/
theorem stock_lower_return_record_static {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {xs : List Nat} (ret : b.term = .ret xs)
    {record : ScanRecord} (records : record ∈ event.output.records) (terminal : record.inst = event.termInst) :
    ∃ rs ps,(xs ++ sretRet f).mapM event.ctx.valueReg? = some rs ∧
      (∀ r ∈ rs,∃ n,r = .vreg n .int) ∧ returnPins f rs.length = some ps ∧
      record.output.emitted = #[.rets (rs.zip ps)] ∧
      Stock.externCtor event.ctx T.gen_return [.regsVec (rs.map (fun r => [r]))]
        ((xs ++ sretRet f).foldl State.mark (scanState record.input record.inst)) =
          .ok (.op .unit,record.output.state) ∧
      SpillInstOk (.rets (rs.zip ps)) ∧
      (∀ i ∈ (record.output.emitted.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))).toList,SpillInstOk i) := by
  obtain ⟨step,recorded,emitted⟩ := stock_lower_retTrap_record_emitted run scope events block (by rw [ret]; rfl) records terminal
  obtain ⟨fuel,trace,rs,ps,enough,helper,chosen,mapping,pins,state,code⟩ :=
    stock_lower_return_record_helper run scope events block ret records terminal recorded emitted
  have context := (stock_lower_record_context run scope events).1
  have virtual : ∀ r ∈ rs,∃ n,r = .vreg n .int := by
    intro r member
    obtain ⟨x,present,lookup⟩ := mapM_mem mapping r member
    exact context.valueReg x r lookup
  have gen := stock_gen_return_call event.ctx ((xs ++ sretRet f).foldl State.mark (scanState record.input record.inst))
    rs ps (by rw [context.func]; exact pins)
  rw [← state] at gen
  refine ⟨rs,ps,mapping,virtual,pins,code,gen,pinned_static virtual pins,?_⟩
  intro i member
  rw [code] at member
  simp only [Array.toList_map,Array.toList_push,Array.toList_empty,List.map_cons,List.map_nil,List.mem_singleton] at member
  subst i
  exact pinned_resolved_static virtual pins result.final.alias

end Backend.Stock.Proof.ReturnStaticDraft
