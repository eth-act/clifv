import FV.Backend.Proof.StockBlockScan
namespace Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- A retained record's source position occurs in the actual scan. -/
theorem ScansSpec.record_inst_mem {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (scanned : ScansSpec exec indices input output) {record : ScanRecord}
    (member : record ∈ output.records) : record.inst ∈ indices := by
  rw [← scanned.order]
  exact List.mem_map.mpr ⟨record,member,rfl⟩

/-- An actual scan of distinct source positions has one record per position.
This connects a derived retained division to any body-family classification at
that original index, without an externally chosen record identity. -/
theorem ScansSpec.record_unique {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (scanned : ScansSpec exec indices input output) (unique : indices.Nodup)
    {r s : ScanRecord} (first : r ∈ output.records) (second : s ∈ output.records)
    (same : r.inst = s.inst) : r = s := by
  induction scanned with
  | nil input => cases first
  | @cons i indices input scan tail head rest ih =>
    have fresh := List.nodup_cons.mp unique
    rcases List.mem_cons.mp first with rfl | first
    · rcases List.mem_cons.mp second with rfl | second
      · rfl
      · have member := rest.record_inst_mem second
        rw [← same] at member
        exact False.elim (fresh.1 member)
    · rcases List.mem_cons.mp second with rfl | second
      · have member := rest.record_inst_mem first
        rw [same] at member
        exact False.elim (fresh.1 member)
      · exact ih fresh.2 first second
end Backend.Stock.Proof
#print axioms Backend.Stock.Proof.ScansSpec.record_inst_mem
#print axioms Backend.Stock.Proof.ScansSpec.record_unique
