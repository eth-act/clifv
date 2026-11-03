import FV.Backend.Proof.StockAcquireScanColorUpper

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- This internal index names the original boundary before one source block. -/
def sourceBlockBoundary (f : Clif.Function) (ranges : Array (Nat × Nat)) (bi : Nat) : Nat :=
  ((f.blocks.zipIdx.take bi).flatMap (blockColorEvents ranges)).length

/-- Actual source construction retains the complete event chunk around the original block boundary. -/
theorem source_block_event_split {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {initial : LState} (built : Backend.buildCtx f = .ok (ctx,ranges,initial))
    {bi : Nat} {block : Clif.Block} (blockAt : f.blocks[bi]? = some block) :
    sourceColorEvents ctx ranges =
      ((f.blocks.zipIdx.take bi).flatMap (blockColorEvents ranges)) ++
      blockColorEvents ranges (block,bi) ++
      ((f.blocks.zipIdx.drop (bi+1)).flatMap (blockColorEvents ranges)) := by
  have found : f.blocks.zipIdx[bi]? = some (block,bi) := by simp only [List.getElem?_zipIdx,blockAt,Option.map_some,Nat.zero_add]
  have inside : bi < f.blocks.zipIdx.length := (List.getElem?_eq_some_iff.mp found).1
  have item : f.blocks.zipIdx[bi] = (block,bi) := (List.getElem?_eq_some_iff.mp found).2
  have parts : f.blocks.zipIdx = f.blocks.zipIdx.take bi ++ (block,bi)::f.blocks.zipIdx.drop (bi+1) := by
    calc
      f.blocks.zipIdx = f.blocks.zipIdx.take bi ++ f.blocks.zipIdx.drop bi := (List.take_append_drop bi _).symm
      _ = _ := by rw [List.drop_eq_getElem_cons inside,item]
  rw [sourceColorEvents,(ctxSpec_of built).func]
  exact (congrArg (List.flatMap (blockColorEvents ranges)) parts).trans (by
    simp only [List.flatMap_append,List.flatMap_cons,List.append_assoc])

/-- The exact original event index contains a boundary rather than a deferred effect. -/
theorem source_block_boundary_lookup {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {initial : LState} (built : Backend.buildCtx f = .ok (ctx,ranges,initial))
    {bi : Nat} {block : Clif.Block} (blockAt : f.blocks[bi]? = some block) :
    (sourceColorEvents ctx ranges)[sourceBlockBoundary f ranges bi]? = some none := by
  rw [source_block_event_split built blockAt]
  simp only [sourceBlockBoundary,blockColorEvents,List.append_assoc,List.cons_append]
  simp

/-- The real terminator color is the exact end of its original block event chunk. -/
theorem source_block_terminal_color {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {initial : LState} (built : Backend.buildCtx f = .ok (ctx,ranges,initial))
    {bi : Nat} {block : Clif.Block} (blockAt : f.blocks[bi]? = some block) :
    (sourceMetadata ctx ranges).entryColor[blockStart f bi+block.body.length]! =
      sourceBlockBoundary f ranges bi+1+(bodyColorEvents (blockStart f bi) block.body.zipIdx).length := by
  have rangesAt := (ctxSpec_of built).ranges bi block blockAt
  have rangesValue : ranges[bi]! = (blockStart f bi,blockStart f bi+block.body.length+1) := by
    simp only [getElem!_def,rangesAt,Option.getD_some]
  have split := source_block_event_split built blockAt
  simp only [blockColorEvents,rangesValue,Nat.add_sub_cancel] at split
  have events : sourceColorEvents ctx ranges =
      (((f.blocks.zipIdx.take bi).flatMap (blockColorEvents ranges)) ++ none::
        bodyColorEvents (blockStart f bi) block.body.zipIdx) ++
      some (blockStart f bi+block.body.length)::
        ((f.blocks.zipIdx.drop (bi+1)).flatMap (blockColorEvents ranges)) := by
    simpa only [List.append_assoc,List.cons_append,List.singleton_append,List.nil_append] using split
  rw [source_color_event_exact built _ _ _ events]
  simp only [List.length_append,List.length_cons,sourceBlockBoundary]
  omega

end Backend.Stock.Proof.Acquire810
