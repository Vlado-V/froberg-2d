import Froberg.QuadraticTargetWitnesses
import Froberg.QuadraticEndpoint

/-! The quadratic endpoint discharges the last low-row input in B.7. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology
variable {K : Type*} [Field K] [CharZero K]

theorem eventually_quadratic_row_four_exact {d : ℕ} (hd : 3≤d) :
    ∀ᶠ h : ℕ in atTop, ∀ᶠ m : ℕ in atTop, ∀ r : ℕ,
      countAlpha d*(h : ℝ)^2*(m : ℝ)^(d-2) ≤ (r : ℝ) →
      QuadraticTargetWitness K d h m r 2 (d-2) := by
  apply eventually_quadratic_row_four_exact_of_endpoint hd
  intro h hh
  apply genericEndpoint_quadratic hh
  simpa only [show h+2-1=h+1 by omega] using upperCount_le_monomial_count hh 2

end Froberg
