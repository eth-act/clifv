import FV.Backend.Proof.StockParameterShape
import FV.Backend.Proof.StockBranchArgumentShape
import FV.Backend.RegallocPerEdge
import FV.Backend.Proof.SpillStep4Run

namespace Backend.Proof.PerEdgeSpill
open Backend Backend.Proof.Spill Backend.Stock.Proof
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The actual indexed edge result, with old argument symbols renamed to the
selected target parameters before successor-entry moves execute. -/
structure EdgeTransferAt (c : CheckCtx) (edges : Array (Array (Array Reg)))
    (b target j : Nat) (args : Array Reg) (tb : VBlock) (out e : AState) : Prop where
  checked : c.edgeAt edges b target j out = .ok e
  formula : e = (c.edgeForget b target out).parCopy (tb.params.toList.map Reg.homeNum) (args.toList.map Reg.homeNum)
  size : e.size = out.size
  parameter : ∀ (i : Nat) (ar p : Reg),args[i]? = some ar → tb.params[i]? = some p →
    ∀ l,Sym.vreg ar.homeNum ∈ (c.edgeForget b target out).get l → Sym.vreg p.homeNum ∈ e.get l
  entry : ∀ l r,Sym.entry r ∈ out.get l → Sym.entry r ∈ e.get l
  other : ∀ l v,v ∉ tb.params.toList.map Reg.homeNum →
    Sym.vreg v ∈ (c.edgeForget b target out).get l → Sym.vreg v ∈ e.get l

private theorem forget_size (c : CheckCtx) (b target : Nat) (out : AState) :
    (c.edgeForget b target out).size = out.size := by
  unfold CheckCtx.edgeForget
  repeat' first | (solve | rfl) | split | (solve | simp [forgetOps])
private theorem forget_entry (c : CheckCtx) (b target : Nat) (out : AState) (l : Loc) (r : Reg)
    (held : Sym.entry r ∈ out.get l) : Sym.entry r ∈ (c.edgeForget b target out).get l := by
  unfold CheckCtx.edgeForget
  repeat' first | exact held | split |
    exact mem_forgetOps held (fun _ _ _ same => by cases same)

private theorem numbers (rs : List Reg) (shape : ∀ r ∈ rs,∃ v,r = .vreg v .int) :
    rs.mapM vregNum = .ok (rs.map Reg.homeNum) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    obtain ⟨v,rfl⟩ := shape r List.mem_cons_self
    simp only [List.mapM_cons,vregNum,List.map_cons,Reg.homeNum]
    rw [ih (fun r hr => shape r (.tail _ hr))]
    rfl

private theorem copy_formula {c : CheckCtx} {vc : VCode} {edges : Array (Array (Array Reg))}
    (code : c.vc = vc) {b target j : Nat} {vb tb : VBlock} {row : Array (Array Reg)} {args : Array Reg}
    (source : vc.blocks[b]? = some vb) (targetBlock : vc.blocks[target]? = some tb)
    (atRow : edges[b]? = some row) (atArgs : row[j]? = some args)
    (arity : args.size = tb.params.size) (argShape : ArgumentShape args) (params : ParameterShape tb.params)
    (a : AState) : c.edgeCopyAt edges b target j a =
      .ok (a.parCopy (tb.params.toList.map Reg.homeNum) (args.toList.map Reg.homeNum)) := by
  unfold CheckCtx.edgeCopyAt
  rw [code,source,targetBlock,atRow]
  simp only [Option.bind_some,atArgs]
  have sizeCheck : ensure (args.size == tb.params.size) (fun _ =>
      s!"edge {vb.label} → {tb.label}: {args.size} arguments for {tb.params.size} parameters") = .ok () := ensure_true (by simp [arity])
  rw [sizeCheck]
  simp only [bind,Except.bind]
  by_cases empty : args.isEmpty = true
  · rw [if_pos empty]
    have argsEmpty : args = #[] := Array.isEmpty_iff.mp empty
    have paramsEmpty : tb.params = #[] := Array.eq_empty_iff_size_eq_zero.mpr (by rw [← arity,argsEmpty]; rfl)
    simp [argsEmpty,paramsEmpty,AState.parCopy]
    have filterTrue : (fun s : List Sym => s.filter (fun _ => true)) = id :=
      funext fun s => List.filter_eq_self.mpr (fun _ _ => rfl)
    rw [filterTrue,Array.map_id]
  · rw [if_neg empty,numbers _ params.1,numbers _ argShape]
    simp only [bind,Except.bind]
    rw [ensure_true (by simpa using params.2)]
    rfl

/-- Every actual edge with the proved vector/parameter metadata passes its
state-independent copy checks and gives the exact parameter-symbol transfer.
This uses the actual selected row, including its index among duplicate edges. -/
theorem edgeAt_of_metadata {c : CheckCtx} {vc : VCode} {edges : Array (Array (Array Reg))}
    (code : c.vc = vc) {b target j : Nat} {vb tb : VBlock} {row : Array (Array Reg)} {args : Array Reg}
    (source : vc.blocks[b]? = some vb) (targetBlock : vc.blocks[target]? = some tb)
    (atRow : edges[b]? = some row) (atArgs : row[j]? = some args)
    (arity : args.size = tb.params.size) (argShape : ArgumentShape args) (params : ParameterShape tb.params)
    (out : AState) : EdgeTransferAt c edges b target j args tb out
      ((c.edgeForget b target out).parCopy (tb.params.toList.map Reg.homeNum) (args.toList.map Reg.homeNum)) := by
  constructor
  · exact copy_formula code source targetBlock atRow atArgs arity argShape params _
  · rfl
  · rw [AState.parCopy_eq]
    rw [Array.size_map]
    exact forget_size _ _ _ _
  · intro i ar p arAt pAt l held
    apply mem_parCopy_add (y := ar.homeNum) ?_ held
    have pairAt : ((tb.params.toList.map Reg.homeNum).zip (args.toList.map Reg.homeNum))[i]? = some (p.homeNum,ar.homeNum) := by
      apply List.getElem?_zip_eq_some.mpr
      constructor
      · simpa only [List.getElem?_map,Array.getElem?_toList,pAt,Option.map_some]
      · simpa only [List.getElem?_map,Array.getElem?_toList,arAt,Option.map_some]
    exact List.mem_of_getElem? pairAt
  · intro l r held
    exact mem_parCopy_keep (forget_entry c b target out l r held) (fun _ _ same => by cases same)
  · intro l v outside held
    exact mem_parCopy_keep held (fun p hp same => by cases same; exact outside hp)

end Backend.Proof.PerEdgeSpill
