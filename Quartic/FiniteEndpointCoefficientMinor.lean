module

public import Quartic.FiniteEndpointCertificate

@[expose] public section

/-! Coefficient minors read directly from the supplied bitsets. The selected
column counts agree without checking a second expanded coefficient table. -/
namespace Quartic.FiniteEndpointCoefficientMinor

theorem count_filter_finRange {n : ℕ} (p : Fin n → Bool) (j : Fin n) :
    ((List.finRange n).filter p).count j = if p j then 1 else 0 := by
  by_cases h : p j = true
  · rw [List.count_filter h,List.count_finRange]
    simp [h]
  · have hmem : j ∉ (List.finRange n).filter p := by simp [List.mem_filter,h]
    rw [List.count_eq_zero.mpr hmem]
    simp [h]

/-- The minor row is obtained by testing exactly its selected original columns. -/
def rows {b r : ℕ} (coefficients : Fin r → ℕ) (columns : Fin r → Fin b)
    (i : Fin r) : List (Fin r) :=
  (List.finRange r).filter (fun j => (coefficients i).testBit (columns j).val)

/-- Literal generator-support counts equal the corresponding coefficient-minor
counts. This retains the exact characteristic-zero polynomial interpretation. -/
theorem counts {b r : ℕ} (coefficients : Fin r → ℕ) (columns : Fin r → Fin b)
    (i j : Fin r) :
    ((List.finRange b).filter (fun k => (coefficients i).testBit k.val)).count
        (columns j) = (rows coefficients columns i).count j := by
  rw [rows,count_filter_finRange,count_filter_finRange]

end Quartic.FiniteEndpointCoefficientMinor
