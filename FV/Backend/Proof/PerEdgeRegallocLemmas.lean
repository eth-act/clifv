module

public import FV.Backend.RegallocPerEdge
public import FV.Backend.Proof.RegallocLemmas
public import FV.Backend.Proof.PerEdgeVCodeSem

@[expose] public section

namespace Backend.Proof.PerEdge
open Backend
variable {c : CheckCtx} {edges : Array (Array (Array Reg))}

/-- Verified edges retain their actual successor index, including duplicates. -/
def EdgesOk (c : CheckCtx) (edges : Array (Array (Array Reg)))
    (ins : Array (Option AState)) (b : Nat) (out : AState) : Prop :=
  ∀ index s,(c.succs[b]?.getD #[])[index]? = some s → ∃ e a',
    c.edgeAt edges b s index out = .ok e ∧ ins[s]? = some (some a') ∧ a'.le e = true

theorem verifyBlock_ok {ins : Array (Option AState)} {b : Nat}
    (h : c.verifyBlockAt edges ins b = .ok ()) :
    ∃ a out,ins[b]? = some (some a) ∧ c.runBlock b a = .ok out ∧ EdgesOk c edges ins b out := by
  unfold CheckCtx.verifyBlockAt at h
  split at h
  · rename_i a ha
    obtain ⟨out,h1,h⟩ := Except.bind_ok h
    refine ⟨a,out,ha,h1,?_⟩
    intro index s hs
    have pair : (s,index) ∈ (c.succs[b]?.getD #[]).zipIdx.toList :=
      List.mem_of_getElem? (i := index) (by simpa using hs)
    obtain ⟨e,h2,h⟩ := Except.bind_ok (forM_ok h (s,index) pair)
    split at h
    · rename_i a' ha'
      exact ⟨e,a',h2,ha',ensure_ok h⟩
    · cases h
  · cases h

theorem verify_ok {ins : Array (Option AState)} (h : c.verifyAt edges ins = .ok ()) :
    (∃ a0,ins[0]? = some (some a0) ∧ a0.le (entryState c.size) = true) ∧
    ∀ b < c.vc.blocks.size,c.verifyBlockAt edges ins b = .ok () := by
  unfold CheckCtx.verifyAt at h
  split at h
  · rename_i a0 ha0
    obtain ⟨h1,h⟩ := Except.seq_ok h
    exact ⟨⟨a0,ha0,ensure_ok h1⟩,fun b hb => forM_ok h b (List.mem_range.mpr hb)⟩
  · cases h

theorem checkAlloc_ok {vc : VCode} {rf : RFunc} (h : checkAllocAt vc edges rf = .ok ()) :
    ∃ succs preds ins,vc.cfg = .ok (succs,preds) ∧ vc.blocks.size ≠ 0 ∧
      rf.blocks.size = vc.blocks.size ∧
      CheckCtx.verifyAt ⟨vc,succs,rf,128+2*rf.spillSlots⟩ edges ins = .ok () := by
  unfold checkAllocAt at h
  obtain ⟨⟨succs,preds⟩,hcfg,h⟩ := Except.bind_ok h
  dsimp only at h
  obtain ⟨h1,h⟩ := Except.seq_ok h
  obtain ⟨h2,h⟩ := Except.seq_ok h
  obtain ⟨_,h⟩ := Except.seq_ok h
  obtain ⟨_,h⟩ := Except.seq_ok h
  obtain ⟨_,h⟩ := Except.seq_ok h
  obtain ⟨_,_,h⟩ := Except.bind_ok h
  obtain ⟨ins,_,h⟩ := Except.bind_ok h
  obtain ⟨_,h⟩ := Except.seq_ok h
  exact ⟨succs,preds,ins,hcfg,by simpa using ensure_ok h1,by simpa using ensure_ok h2,h⟩

/-- An accepting indexed edge copy refines the actual per-successor VCode copy
and preserves the concrete-store invariant. No allocator result is trusted. -/
theorem edgeCopy_ok {V : Type} {keep : Reg → V → V} {b s index : Nat} {out e : AState}
    (h : c.edgeCopyAt edges b s index out = .ok e) {m : Loc → V} {ρ : Nat → V} {r₀ : Reg → V}
    (hi : Inv keep out m ρ r₀) :
    ∃ ρ',edgeEnvAt c.vc edges b s index ρ = some ρ' ∧ Inv keep e m ρ' r₀ := by
  unfold CheckCtx.edgeCopyAt at h
  split at h
  · rename_i vb sb hb hs
    split at h
    · rename_i args ha
      obtain ⟨h1,h⟩ := Except.seq_ok h
      have hsz : args.size = sb.params.size := by simpa using ensure_ok h1
      split at h
      · rename_i he
        have e1 : args.toList = [] := by simpa using he
        have e2 : sb.params.toList = [] := by
          have : sb.params.size = 0 := by rw [← hsz]; simpa using he
          simpa using this
        refine ⟨ρ,?_,?_⟩
        · have empty : parCopyEnv ρ [] [] = ρ := by funext v; rfl
          simp [edgeEnvAt,hs,ha,hsz,e1,e2,Except.toOption,List.mapM_nil,empty]
        · rw [(Except.ok.inj h).symm]; exact hi
      · obtain ⟨ps,hps,h⟩ := Except.bind_ok h
        obtain ⟨xs,hxs,h⟩ := Except.bind_ok h
        obtain ⟨h3,h⟩ := Except.seq_ok h
        refine ⟨parCopyEnv ρ ps xs,?_,?_⟩
        · simp [edgeEnvAt,hs,ha,hsz,hps,hxs,Except.toOption]
        · rw [(Except.ok.inj h).symm]
          exact Inv_parCopy (by simpa using ensure_ok h3) hi
    · cases h
  · cases h
  · cases h

theorem edge_ok {V : Type} {keep : Reg → V → V} {b s index : Nat} {out e : AState}
    (h : c.edgeAt edges b s index out = .ok e) {m : Loc → V} {ρ : Nat → V} {r₀ : Reg → V}
    (hi : Inv keep (c.edgeForget b s out) m ρ r₀) :
    ∃ ρ',edgeEnvAt c.vc edges b s index ρ = some ρ' ∧ Inv keep e m ρ' r₀ := edgeCopy_ok h hi
end Backend.Proof.PerEdge
