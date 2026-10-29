module

public import FV.Backend.Proof.StockLinearCfgTrace
public import FV.Backend.Proof.StockCfgJumpDemand

@[expose] public section

namespace Backend.Stock.Proof.LinearCfg
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Reverse traversal connects successive original scans without a demand
certificate or a value-forwarding restriction on the source jumps. -/
theorem three_scan_links {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {entry middle target : Clif.Block} {first second : Clif.BlockCall}
    (blocks : f.blocks = [entry,middle,target])
    (firstJump : entry.term = .jump first) (secondJump : middle.term = .jump second)
    (order : result.order = ⟨#[.original 0,.original 1,.original 2],#[#[1],#[2],#[]]⟩) :
    ∃ (es ms ts : BlockScanEvent),result.blockScans = #[ts,ms,es] ∧
      es.block = 0 ∧ ms.block = 1 ∧ ts.block = 2 ∧
      es.isBranch = true ∧ ms.isBranch = true ∧
      (∀ (x : Nat),ms.output.state.demand[x]! ≤ es.input.demand[x]!) ∧
      (∀ (x : Nat),ts.output.state.demand[x]! ≤ ms.input.demand[x]!) := by
  obtain ⟨ranges,input,tc,mc,ec,td,md,ed,build,tr,mr,er,events⟩ := three_original_scans run order
  have to := stock_lowerBlockCore_scanOrigin tr
  have mo := stock_lowerBlockCore_scanOrigin mr
  have eo := stock_lowerBlockCore_scanOrigin er
  have ev : f.blocks[0]! = entry := by simp [blocks]
  have mv : f.blocks[1]! = middle := by simp [blocks]
  rw [ev] at er
  rw [mv] at mr
  have func := (buildCtx_mappedInv scope build).func
  obtain ⟨eb,em⟩ := Control.jump_core_input_demand_mono func
    (by simp [blocks] : f.blocks[0]? = some entry) firstJump
    (by simp [order] : result.order.nodes[1]? = some (.original 1)) er
  obtain ⟨mb,mm⟩ := Control.jump_core_input_demand_mono func
    (by simp [blocks] : f.blocks[1]? = some middle) secondJump
    (by simp [order] : result.order.nodes[2]? = some (.original 2)) mr
  refine ⟨ec.scan,mc.scan,tc.scan,events,eo.2.2.1,mo.2.2.1,to.2.2.1,eb,mb,?_,?_⟩
  · simpa only [mo.1] using em
  · simpa only [to.1] using mm

private theorem event_eq {events : Array BlockScanEvent} {es ms ts event : BlockScanEvent}
    (all : events = #[ts,ms,es]) (eb : es.block = 0) (mb : ms.block = 1) (tb : ts.block = 2)
    (member : event ∈ events.toList) {bi : Nat} (block : event.block = bi) :
    (bi = 0 → event = es) ∧ (bi = 1 → event = ms) ∧ (bi = 2 → event = ts) := by
  rw [all] at member
  change event ∈ [ts,ms,es] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (rfl | rfl | rfl) <;> constructor
  all_goals first | (constructor <;> intro h <;> first | rfl | omega) | (intro h; first | rfl | omega)

/-- A real predecessor body retains every demand of the next block's output
scan. The relation is derived from the one compiler run and retained events. -/
theorem jump_successor_demand {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {entry middle target : Clif.Block} {first second : Clif.BlockCall}
    (blocks : f.blocks = [entry,middle,target])
    (firstJump : entry.term = .jump first) (secondJump : middle.term = .jump second)
    (order : result.order = ⟨#[.original 0,.original 1,.original 2],#[#[1],#[2],#[]]⟩)
    {predecessor successor : BlockScanEvent} (pe : predecessor ∈ result.blockScans.toList)
    (se : successor ∈ result.blockScans.toList)
    (adjacent : (predecessor.block = 0 ∧ successor.block = 1) ∨
      (predecessor.block = 1 ∧ successor.block = 2))
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f predecessor b term body) :
    ∀ (x : Nat),successor.output.state.demand[x]! ≤ term.output.state.demand[x]! := by
  obtain ⟨es,ms,ts,events,eb,mb,tb,ebr,mbr,em,mm⟩ :=
    three_scan_links run scope blocks firstJump secondJump order
  rcases adjacent with ⟨pb,sb⟩ | ⟨pb,sb⟩
  · have p := (event_eq events eb mb tb pe pb).1 rfl
    have s := (event_eq events eb mb tb se sb).2.1 rfl
    subst predecessor; subst successor
    rw [(Control.stock_branch_scan_body_code split ebr).2,split.termInput]
    exact em
  · have p := (event_eq events eb mb tb pe pb).2.1 rfl
    have s := (event_eq events eb mb tb se sb).2.2 rfl
    subst predecessor; subst successor
    rw [(Control.stock_branch_scan_body_code split mbr).2,split.termInput]
    exact mm

end Backend.Stock.Proof.LinearCfg
