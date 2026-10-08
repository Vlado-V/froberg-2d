import Quartic.Generic
import Quartic.Counts

noncomputable section

namespace Quartic

variable {K : Type*} [Field K] (n : ℕ)

theorem expectedDimension_eq_chi_toNat (r : ℕ) :
    expectedDimension n r = (Counts.chi n r).toNat := rfl

theorem full_quadratic_space_quotient :
    Module.finrank K (QuarticQuotient K n (Forms K n 2)) = 0 := by
  change Module.finrank K ((Forms K n 4) ⧸ quarticProducts K n (Forms K n 2)) = 0
  rw [quarticProducts_all]
  exact Module.finrank_zero_of_subsingleton

theorem full_generator_witness : QuarticWitness K n ((n + 1).choose 2) := by
  refine ⟨Forms K n 2, le_rfl, finrank_quadrics K n, ?_⟩
  rw [full_quadratic_space_quotient, expectedDimension_eq_chi_toNat,
    Int.toNat_of_nonpos (Counts.full_quadratic_count_chi_nonpos n)]

/-- In one variable the generic theorem is completely proved for every count. -/
theorem generic_one_variable (r : ℕ) (hr : r ≤ Nat.choose 2 2) : GenericQuartic K 1 r := by
  have hr' : r ≤ 1 := by simpa using hr
  interval_cases r
  · exact generic_zero_generators K 1
  · exact generic_one_generator K 1 (by omega)

end Quartic
